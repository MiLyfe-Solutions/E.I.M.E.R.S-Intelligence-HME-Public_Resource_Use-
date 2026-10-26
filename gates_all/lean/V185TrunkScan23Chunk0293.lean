import V185TrunkScan23Chunk0292

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1733275 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_1733275 : Nat := 118140960795 + 1733275 * 2 ^ 59
def prefixEnd_1733275 : Nat := 4983230072969 + 3 ^ 40 * 1733275 * 2
def baseEnd_1733275 : Nat := 890003181421811287291319

theorem tailTrace_1733275 : CollatzResearch.WordTrace tailWord_1733275 prefixEnd_1733275 890003181421811287291319 := by
  unfold tailWord_1733275
  simp only [CollatzResearch.WordTrace]
  refine ⟨63217732795648169647769279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42145155197098779765179519 63217732795648169647769279)
  ·
    refine ⟨94826599193472254471653919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63217732795648169647769279 94826599193472254471653919)
    ·
      refine ⟨142239898790208381707480879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94826599193472254471653919 142239898790208381707480879)
      ·
        refine ⟨213359848185312572561221319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142239898790208381707480879 213359848185312572561221319)
        ·
          refine ⟨320039772277968858841831979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213359848185312572561221319 320039772277968858841831979)
          ·
            refine ⟨480059658416953288262747969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320039772277968858841831979 480059658416953288262747969)
            ·
              refine ⟨360044743812714966197060977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480059658416953288262747969 360044743812714966197060977)
              ·
                refine ⟨270033557859536224647795733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360044743812714966197060977 270033557859536224647795733)
                ·
                  refine ⟨12657823024665760530365425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270033557859536224647795733 12657823024665760530365425)
                  ·
                    refine ⟨9493367268499320397774069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12657823024665760530365425 9493367268499320397774069)
                    ·
                      refine ⟨890003181421811287291319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9493367268499320397774069 890003181421811287291319)
                      ·
                        rfl

theorem cell23_1733275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_1733275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733275 prefixEnd_1733275 := by exact prefixLift 1733275
  have htrace : WordTrace (prefixWord ++ tailWord_1733275) baseStart_1733275 baseEnd_1733275 := by
    simpa [prefixWord, tailWord_1733275, baseEnd_1733275] using wordTrace_append hprefix tailTrace_1733275
  have hstable : (prefixWord ++ tailWord_1733275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733275).length < 2 ^ (prefixWord ++ tailWord_1733275).sum := by decide
  have hdescent : baseEnd_1733275 < baseStart_1733275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733280 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 1, 2, 2]
def baseStart_1733280 : Nat := 118140960795 + 1733280 * 2 ^ 59
def prefixEnd_1733280 : Nat := 4983230072969 + 3 ^ 40 * 1733280 * 2
def baseEnd_1733280 : Nat := 890005748825083767728797

theorem tailTrace_1733280 : CollatzResearch.WordTrace tailWord_1733280 prefixEnd_1733280 890005748825083767728797 := by
  unfold tailWord_1733280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608957580315027750850647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42145276773753370334467529 31608957580315027750850647)
  ·
    refine ⟨47413436370472541626275971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31608957580315027750850647 47413436370472541626275971)
    ·
      refine ⟨71120154555708812439413957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47413436370472541626275971 71120154555708812439413957)
      ·
        refine ⟨13335028979195402332390117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71120154555708812439413957 13335028979195402332390117)
        ·
          refine ⟨2500317933599137937323147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13335028979195402332390117 2500317933599137937323147)
          ·
            refine ⟨3750476900398706905984721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500317933599137937323147 3750476900398706905984721)
            ·
              refine ⟨2812857675299030179488541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750476900398706905984721 2812857675299030179488541)
              ·
                refine ⟨1054821628237136317308203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2812857675299030179488541 1054821628237136317308203)
                ·
                  refine ⟨1582232442355704475962305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054821628237136317308203 1582232442355704475962305)
                  ·
                    refine ⟨1186674331766778356971729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1582232442355704475962305 1186674331766778356971729)
                    ·
                      refine ⟨890005748825083767728797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186674331766778356971729 890005748825083767728797)
                      ·
                        rfl

theorem cell23_1733280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_1733280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733280 prefixEnd_1733280 := by exact prefixLift 1733280
  have htrace : WordTrace (prefixWord ++ tailWord_1733280) baseStart_1733280 baseEnd_1733280 := by
    simpa [prefixWord, tailWord_1733280, baseEnd_1733280] using wordTrace_append hprefix tailTrace_1733280
  have hstable : (prefixWord ++ tailWord_1733280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733280).length < 2 ^ (prefixWord ++ tailWord_1733280).sum := by decide
  have hdescent : baseEnd_1733280 < baseStart_1733280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733290 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1733290 : Nat := 118140960795 + 1733290 * 2 ^ 59
def prefixEnd_1733290 : Nat := 4983230072969 + 3 ^ 40 * 1733290 * 2
def baseEnd_1733290 : Nat := 296670294543876242867917

theorem tailTrace_1733290 : CollatzResearch.WordTrace tailWord_1733290 prefixEnd_1733290 296670294543876242867917 := by
  unfold tailWord_1733290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15804569972648456802391331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42145519927062551473043549 15804569972648456802391331)
  ·
    refine ⟨23706854958972685203586997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15804569972648456802391331 23706854958972685203586997)
    ·
      refine ⟨2222517652403689237836281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23706854958972685203586997 2222517652403689237836281)
      ·
        refine ⟨1666888239302766928377211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222517652403689237836281 1666888239302766928377211)
        ·
          refine ⟨2500332358954150392565817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666888239302766928377211 2500332358954150392565817)
          ·
            refine ⟨1875249269215612794424363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500332358954150392565817 1875249269215612794424363)
            ·
              refine ⟨2812873903823419191636545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875249269215612794424363 2812873903823419191636545)
              ·
                refine ⟨2109655427867564393727409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812873903823419191636545 2109655427867564393727409)
                ·
                  refine ⟨1582241570900673295295557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109655427867564393727409 1582241570900673295295557)
                  ·
                    refine ⟨296670294543876242867917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1582241570900673295295557 296670294543876242867917)
                    ·
                      rfl

theorem cell23_1733290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1733290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733290 prefixEnd_1733290 := by exact prefixLift 1733290
  have htrace : WordTrace (prefixWord ++ tailWord_1733290) baseStart_1733290 baseEnd_1733290 := by
    simpa [prefixWord, tailWord_1733290, baseEnd_1733290] using wordTrace_append hprefix tailTrace_1733290
  have hstable : (prefixWord ++ tailWord_1733290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733290).length < 2 ^ (prefixWord ++ tailWord_1733290).sum := by decide
  have hdescent : baseEnd_1733290 < baseStart_1733290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733312 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_1733312 : Nat := 118140960795 + 1733312 * 2 ^ 59
def prefixEnd_1733312 : Nat := 4983230072969 + 3 ^ 40 * 1733312 * 2
def baseEnd_1733312 : Nat := 296674060068675880842883

theorem tailTrace_1733312 : CollatzResearch.WordTrace tailWord_1733312 prefixEnd_1733312 296674060068675880842883 := by
  unfold tailWord_1733312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31609541148257062483433095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42146054864342749977910793 31609541148257062483433095)
  ·
    refine ⟨47414311722385593725149643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31609541148257062483433095 47414311722385593725149643)
    ·
      refine ⟨71121467583578390587724465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47414311722385593725149643 71121467583578390587724465)
      ·
        refine ⟨53341100687683792940793349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71121467583578390587724465 53341100687683792940793349)
        ·
          refine ⟨10001456378940711176398753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53341100687683792940793349 10001456378940711176398753)
          ·
            refine ⟨7501092284205533382299065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001456378940711176398753 7501092284205533382299065)
            ·
              refine ⟨5625819213154150036724299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501092284205533382299065 5625819213154150036724299)
              ·
                refine ⟨8438728819731225055086449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625819213154150036724299 8438728819731225055086449)
                ·
                  refine ⟨6329046614798418791314837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438728819731225055086449 6329046614798418791314837)
                  ·
                    refine ⟨296674060068675880842883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6329046614798418791314837 296674060068675880842883)
                    ·
                      rfl

theorem cell23_1733312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_1733312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733312 prefixEnd_1733312 := by exact prefixLift 1733312
  have htrace : WordTrace (prefixWord ++ tailWord_1733312) baseStart_1733312 baseEnd_1733312 := by
    simpa [prefixWord, tailWord_1733312, baseEnd_1733312] using wordTrace_append hprefix tailTrace_1733312
  have hstable : (prefixWord ++ tailWord_1733312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733312).length < 2 ^ (prefixWord ++ tailWord_1733312).sum := by decide
  have hdescent : baseEnd_1733312 < baseStart_1733312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733315 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1733315 : Nat := 118140960795 + 1733315 * 2 ^ 59
def prefixEnd_1733315 : Nat := 4983230072969 + 3 ^ 40 * 1733315 * 2
def baseEnd_1733315 : Nat := 890023720647991130791135

theorem tailTrace_1733315 : CollatzResearch.WordTrace tailWord_1733315 prefixEnd_1733315 890023720647991130791135 := by
  unfold tailWord_1733315
  simp only [CollatzResearch.WordTrace]
  refine ⟨63219191715503256479225399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42146127810335504319483599 63219191715503256479225399)
  ·
    refine ⟨94828787573254884718838099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63219191715503256479225399 94828787573254884718838099)
    ·
      refine ⟨142243181359882327078257149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94828787573254884718838099 142243181359882327078257149)
      ·
        refine ⟨53341193009955872654346431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142243181359882327078257149 53341193009955872654346431)
        ·
          refine ⟨80011789514933808981519647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53341193009955872654346431 80011789514933808981519647)
          ·
            refine ⟨120017684272400713472279471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80011789514933808981519647 120017684272400713472279471)
            ·
              refine ⟨180026526408601070208419207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120017684272400713472279471 180026526408601070208419207)
              ·
                refine ⟨270039789612901605312628811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180026526408601070208419207 270039789612901605312628811)
                ·
                  refine ⟨405059684419352407968943217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270039789612901605312628811 405059684419352407968943217)
                  ·
                    refine ⟨303794763314514305976707413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 405059684419352407968943217 303794763314514305976707413)
                    ·
                      refine ⟨890023720647991130791135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 303794763314514305976707413 890023720647991130791135)
                      ·
                        rfl

theorem cell23_1733315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1733315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733315 prefixEnd_1733315 := by exact prefixLift 1733315
  have htrace : WordTrace (prefixWord ++ tailWord_1733315) baseStart_1733315 baseEnd_1733315 := by
    simpa [prefixWord, tailWord_1733315, baseEnd_1733315] using wordTrace_append hprefix tailTrace_1733315
  have hstable : (prefixWord ++ tailWord_1733315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733315).length < 2 ^ (prefixWord ++ tailWord_1733315).sum := by decide
  have hdescent : baseEnd_1733315 < baseStart_1733315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733319 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_1733319 : Nat := 118140960795 + 1733319 * 2 ^ 59
def prefixEnd_1733319 : Nat := 4983230072969 + 3 ^ 40 * 1733319 * 2
def baseEnd_1733319 : Nat := 890025774570609115141117

theorem tailTrace_1733319 : CollatzResearch.WordTrace tailWord_1733319 prefixEnd_1733319 890025774570609115141117 := by
  unfold tailWord_1733319
  simp only [CollatzResearch.WordTrace]
  refine ⟨63219337607488765162371011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42146225071659176774914007 63219337607488765162371011)
  ·
    refine ⟨94829006411233147743556517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63219337607488765162371011 94829006411233147743556517)
    ·
      refine ⟨17780438702106215201916847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94829006411233147743556517 17780438702106215201916847)
      ·
        refine ⟨26670658053159322802875271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17780438702106215201916847 26670658053159322802875271)
        ·
          refine ⟨40005987079738984204312907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26670658053159322802875271 40005987079738984204312907)
          ·
            refine ⟨60008980619608476306469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40005987079738984204312907 60008980619608476306469361)
            ·
              refine ⟨45006735464706357229852021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60008980619608476306469361 45006735464706357229852021)
              ·
                refine ⟨4219381449816220990298627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45006735464706357229852021 4219381449816220990298627)
                ·
                  refine ⟨6329072174724331485447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219381449816220990298627 6329072174724331485447941)
                  ·
                    refine ⟨1186701032760812153521489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329072174724331485447941 1186701032760812153521489)
                    ·
                      refine ⟨890025774570609115141117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186701032760812153521489 890025774570609115141117)
                      ·
                        rfl

theorem cell23_1733319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_1733319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733319 prefixEnd_1733319 := by exact prefixLift 1733319
  have htrace : WordTrace (prefixWord ++ tailWord_1733319) baseStart_1733319 baseEnd_1733319 := by
    simpa [prefixWord, tailWord_1733319, baseEnd_1733319] using wordTrace_append hprefix tailTrace_1733319
  have hstable : (prefixWord ++ tailWord_1733319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733319).length < 2 ^ (prefixWord ++ tailWord_1733319).sum := by decide
  have hdescent : baseEnd_1733319 < baseStart_1733319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733336 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_1733336 : Nat := 118140960795 + 1733336 * 2 ^ 59
def prefixEnd_1733336 : Nat := 4983230072969 + 3 ^ 40 * 1733336 * 2
def baseEnd_1733336 : Nat := 890034503741735548628539

theorem tailTrace_1733336 : CollatzResearch.WordTrace tailWord_1733336 prefixEnd_1733336 890034503741735548628539 := by
  unfold tailWord_1733336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31609978824213588532869931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42146638432284784710493241 31609978824213588532869931)
  ·
    refine ⟨47414968236320382799304897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31609978824213588532869931 47414968236320382799304897)
    ·
      refine ⟨35561226177240287099478673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47414968236320382799304897 35561226177240287099478673)
      ·
        refine ⟨26670919632930215324609005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35561226177240287099478673 26670919632930215324609005)
        ·
          refine ⟨10001594862348830746728377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26670919632930215324609005 10001594862348830746728377)
          ·
            refine ⟨7501196146761623060046283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001594862348830746728377 7501196146761623060046283)
            ·
              refine ⟨11251794220142434590069425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501196146761623060046283 11251794220142434590069425)
              ·
                refine ⟨8438845665106825942552069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11251794220142434590069425 8438845665106825942552069)
                ·
                  refine ⟨1582283562207529864228513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8438845665106825942552069 1582283562207529864228513)
                  ·
                    refine ⟨1186712671655647398171385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1582283562207529864228513 1186712671655647398171385)
                    ·
                      refine ⟨890034503741735548628539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186712671655647398171385 890034503741735548628539)
                      ·
                        rfl

theorem cell23_1733336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_1733336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733336 prefixEnd_1733336 := by exact prefixLift 1733336
  have htrace : WordTrace (prefixWord ++ tailWord_1733336) baseStart_1733336 baseEnd_1733336 := by
    simpa [prefixWord, tailWord_1733336, baseEnd_1733336] using wordTrace_append hprefix tailTrace_1733336
  have hstable : (prefixWord ++ tailWord_1733336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733336).length < 2 ^ (prefixWord ++ tailWord_1733336).sum := by decide
  have hdescent : baseEnd_1733336 < baseStart_1733336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733359 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 7]
def baseStart_1733359 : Nat := 118140960795 + 1733359 * 2 ^ 59
def prefixEnd_1733359 : Nat := 4983230072969 + 3 ^ 40 * 1733359 * 2
def baseEnd_1733359 : Nat := 98894034866309884293437

theorem tailTrace_1733359 : CollatzResearch.WordTrace tailWord_1733359 prefixEnd_1733359 98894034866309884293437 := by
  unfold tailWord_1733359
  simp only [CollatzResearch.WordTrace]
  refine ⟨63220796527343851993827131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42147197684895901329218087 63220796527343851993827131)
  ·
    refine ⟨94831194791015777990740697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63220796527343851993827131 94831194791015777990740697)
    ·
      refine ⟨71123396093261833493055523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94831194791015777990740697 71123396093261833493055523)
      ·
        refine ⟨106685094139892750239583285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71123396093261833493055523 106685094139892750239583285)
        ·
          refine ⟨10001727575614945334960933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106685094139892750239583285 10001727575614945334960933)
          ·
            refine ⟨1875323920427802250305175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10001727575614945334960933 1875323920427802250305175)
            ·
              refine ⟨2812985880641703375457763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875323920427802250305175 2812985880641703375457763)
              ·
                refine ⟨4219478820962555063186645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812985880641703375457763 4219478820962555063186645)
                ·
                  refine ⟨98894034866309884293437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4219478820962555063186645 98894034866309884293437)
                  ·
                    rfl

theorem cell23_1733359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 7].length) (baseStart_1733359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733359 prefixEnd_1733359 := by exact prefixLift 1733359
  have htrace : WordTrace (prefixWord ++ tailWord_1733359) baseStart_1733359 baseEnd_1733359 := by
    simpa [prefixWord, tailWord_1733359, baseEnd_1733359] using wordTrace_append hprefix tailTrace_1733359
  have hstable : (prefixWord ++ tailWord_1733359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733359).length < 2 ^ (prefixWord ++ tailWord_1733359).sum := by decide
  have hdescent : baseEnd_1733359 < baseStart_1733359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733364 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1733364 : Nat := 118140960795 + 1733364 * 2 ^ 59
def prefixEnd_1733364 : Nat := 4983230072969 + 3 ^ 40 * 1733364 * 2
def baseEnd_1733364 : Nat := 890048881200061439078411

theorem tailTrace_1733364 : CollatzResearch.WordTrace tailWord_1733364 prefixEnd_1733364 890048881200061439078411 := by
  unfold tailWord_1733364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31610489446162868923879573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42147319261550491898506097 31610489446162868923879573)
  ·
    refine ⟨1481741692788884480806855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31610489446162868923879573 1481741692788884480806855)
    ·
      refine ⟨2222612539183326721210283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481741692788884480806855 2222612539183326721210283)
      ·
        refine ⟨3333918808774990081815425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222612539183326721210283 3333918808774990081815425)
        ·
          refine ⟨2500439106581242561361569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333918808774990081815425 2500439106581242561361569)
          ·
            refine ⟨1875329329935931921021177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500439106581242561361569 1875329329935931921021177)
            ·
              refine ⟨1406496997451948940765883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875329329935931921021177 1406496997451948940765883)
              ·
                refine ⟨2109745496177923411148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406496997451948940765883 2109745496177923411148825)
                ·
                  refine ⟨1582309122133442558361619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109745496177923411148825 1582309122133442558361619)
                  ·
                    refine ⟨2373463683200163837542429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582309122133442558361619 2373463683200163837542429)
                    ·
                      refine ⟨890048881200061439078411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373463683200163837542429 890048881200061439078411)
                      ·
                        rfl

theorem cell23_1733364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1733364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733364 prefixEnd_1733364 := by exact prefixLift 1733364
  have htrace : WordTrace (prefixWord ++ tailWord_1733364) baseStart_1733364 baseEnd_1733364 := by
    simpa [prefixWord, tailWord_1733364, baseEnd_1733364] using wordTrace_append hprefix tailTrace_1733364
  have hstable : (prefixWord ++ tailWord_1733364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733364).length < 2 ^ (prefixWord ++ tailWord_1733364).sum := by decide
  have hdescent : baseEnd_1733364 < baseStart_1733364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733409 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1733409 : Nat := 118140960795 + 1733409 * 2 ^ 59
def prefixEnd_1733409 : Nat := 4983230072969 + 3 ^ 40 * 1733409 * 2
def baseEnd_1733409 : Nat := 890071987829513763015703

theorem tailTrace_1733409 : CollatzResearch.WordTrace tailWord_1733409 prefixEnd_1733409 890071987829513763015703 := by
  unfold tailWord_1733409
  simp only [CollatzResearch.WordTrace]
  refine ⟨63222620177162710533147281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42148413451441807022098187 63222620177162710533147281)
  ·
    refine ⟨47416965132872032899860461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63222620177162710533147281 47416965132872032899860461)
    ·
      refine ⟨17781361924827012337447673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47416965132872032899860461 17781361924827012337447673)
      ·
        refine ⟨13336021443620259253085755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17781361924827012337447673 13336021443620259253085755)
        ·
          refine ⟨20004032165430388879628633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13336021443620259253085755 20004032165430388879628633)
          ·
            refine ⟨15003024124072791659721475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20004032165430388879628633 15003024124072791659721475)
            ·
              refine ⟨22504536186109187489582213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15003024124072791659721475 22504536186109187489582213)
              ·
                refine ⟨4219600534895472654296665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22504536186109187489582213 4219600534895472654296665)
                ·
                  refine ⟨3164700401171604490722499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4219600534895472654296665 3164700401171604490722499)
                  ·
                    refine ⟨4747050601757406736083749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164700401171604490722499 4747050601757406736083749)
                    ·
                      refine ⟨890071987829513763015703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4747050601757406736083749 890071987829513763015703)
                      ·
                        rfl

theorem cell23_1733409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1733409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733409 prefixEnd_1733409 := by exact prefixLift 1733409
  have htrace : WordTrace (prefixWord ++ tailWord_1733409) baseStart_1733409 baseEnd_1733409 := by
    simpa [prefixWord, tailWord_1733409, baseEnd_1733409] using wordTrace_append hprefix tailTrace_1733409
  have hstable : (prefixWord ++ tailWord_1733409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733409).length < 2 ^ (prefixWord ++ tailWord_1733409).sum := by decide
  have hdescent : baseEnd_1733409 < baseStart_1733409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733426 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_1733426 : Nat := 118140960795 + 1733426 * 2 ^ 59
def prefixEnd_1733426 : Nat := 4983230072969 + 3 ^ 40 * 1733426 * 2
def baseEnd_1733426 : Nat := 890080717000640196503125

theorem tailTrace_1733426 : CollatzResearch.WordTrace tailWord_1733426 prefixEnd_1733426 890080717000640196503125 := by
  unfold tailWord_1733426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805810054525280609129033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42148826812067414957677421 15805810054525280609129033)
  ·
    refine ⟨11854357540893960456846775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805810054525280609129033 11854357540893960456846775)
    ·
      refine ⟨17781536311340940685270163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11854357540893960456846775 17781536311340940685270163)
      ·
        refine ⟨26672304467011411027905245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17781536311340940685270163 26672304467011411027905245)
        ·
          refine ⟨10002114175129279135464467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26672304467011411027905245 10002114175129279135464467)
          ·
            refine ⟨15003171262693918703196701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10002114175129279135464467 15003171262693918703196701)
            ·
              refine ⟨5626189223510219513698763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15003171262693918703196701 5626189223510219513698763)
              ·
                refine ⟨8439283835265329270548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626189223510219513698763 8439283835265329270548145)
                ·
                  refine ⟨6329462876448996952911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8439283835265329270548145 6329462876448996952911109)
                  ·
                    refine ⟨1186774289334186928670833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6329462876448996952911109 1186774289334186928670833)
                    ·
                      refine ⟨890080717000640196503125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186774289334186928670833 890080717000640196503125)
                      ·
                        rfl

theorem cell23_1733426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_1733426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733426 prefixEnd_1733426 := by exact prefixLift 1733426
  have htrace : WordTrace (prefixWord ++ tailWord_1733426) baseStart_1733426 baseEnd_1733426 := by
    simpa [prefixWord, tailWord_1733426, baseEnd_1733426] using wordTrace_append hprefix tailTrace_1733426
  have hstable : (prefixWord ++ tailWord_1733426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733426).length < 2 ^ (prefixWord ++ tailWord_1733426).sum := by decide
  have hdescent : baseEnd_1733426 < baseStart_1733426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733466 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_1733466 : Nat := 118140960795 + 1733466 * 2 ^ 59
def prefixEnd_1733466 : Nat := 4983230072969 + 3 ^ 40 * 1733466 * 2
def baseEnd_1733466 : Nat := 98900139580757782222549

theorem tailTrace_1733466 : CollatzResearch.WordTrace tailWord_1733466 prefixEnd_1733466 98900139580757782222549 := by
  unfold tailWord_1733466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806174784489052316993063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42149799425304139511981501 15806174784489052316993063)
  ·
    refine ⟨23709262176733578475489595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15806174784489052316993063 23709262176733578475489595)
    ·
      refine ⟨35563893265100367713234393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23709262176733578475489595 35563893265100367713234393)
      ·
        refine ⟨26672919948825275784925795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35563893265100367713234393 26672919948825275784925795)
        ·
          refine ⟨40009379923237913677388693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26672919948825275784925795 40009379923237913677388693)
          ·
            refine ⟨1875439683901777203627595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40009379923237913677388693 1875439683901777203627595)
            ·
              refine ⟨2813159525852665805441393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875439683901777203627595 2813159525852665805441393)
              ·
                refine ⟨2109869644389499354081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2813159525852665805441393 2109869644389499354081045)
                ·
                  refine ⟨98900139580757782222549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2109869644389499354081045 98900139580757782222549)
                  ·
                    rfl

theorem cell23_1733466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_1733466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733466 prefixEnd_1733466 := by exact prefixLift 1733466
  have htrace : WordTrace (prefixWord ++ tailWord_1733466) baseStart_1733466 baseEnd_1733466 := by
    simpa [prefixWord, tailWord_1733466, baseEnd_1733466] using wordTrace_append hprefix tailTrace_1733466
  have hstable : (prefixWord ++ tailWord_1733466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733466).length < 2 ^ (prefixWord ++ tailWord_1733466).sum := by decide
  have hdescent : baseEnd_1733466 < baseStart_1733466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733493 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1733493 : Nat := 118140960795 + 1733493 * 2 ^ 59
def prefixEnd_1733493 : Nat := 4983230072969 + 3 ^ 40 * 1733493 * 2
def baseEnd_1733493 : Nat := 890115120204491434365317

theorem tailTrace_1733493 : CollatzResearch.WordTrace tailWord_1733493 prefixEnd_1733493 890115120204491434365317 := by
  unfold tailWord_1733493
  simp only [CollatzResearch.WordTrace]
  refine ⟨63225683908858392879205133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42150455939238928586136755 63225683908858392879205133)
  ·
    refine ⟨23709631465821897329701925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63225683908858392879205133 23709631465821897329701925)
    ·
      refine ⟨4445555899841605749319111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23709631465821897329701925 4445555899841605749319111)
      ·
        refine ⟨6668333849762408623978667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445555899841605749319111 6668333849762408623978667)
        ·
          refine ⟨10002500774643612935968001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668333849762408623978667 10002500774643612935968001)
          ·
            refine ⟨7501875580982709701976001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10002500774643612935968001 7501875580982709701976001)
            ·
              refine ⟨5626406685737032276482001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501875580982709701976001 5626406685737032276482001)
              ·
                refine ⟨4219805014302774207361501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626406685737032276482001 4219805014302774207361501)
                ·
                  refine ⟨1582426880363540327760563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4219805014302774207361501 1582426880363540327760563)
                  ·
                    refine ⟨2373640320545310491640845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582426880363540327760563 2373640320545310491640845)
                    ·
                      refine ⟨890115120204491434365317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373640320545310491640845 890115120204491434365317)
                      ·
                        rfl

theorem cell23_1733493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1733493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733493 prefixEnd_1733493 := by exact prefixLift 1733493
  have htrace : WordTrace (prefixWord ++ tailWord_1733493) baseStart_1733493 baseEnd_1733493 := by
    simpa [prefixWord, tailWord_1733493, baseEnd_1733493] using wordTrace_append hprefix tailTrace_1733493
  have hstable : (prefixWord ++ tailWord_1733493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733493).length < 2 ^ (prefixWord ++ tailWord_1733493).sum := by decide
  have hdescent : baseEnd_1733493 < baseStart_1733493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733499 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4]
def baseStart_1733499 : Nat := 118140960795 + 1733499 * 2 ^ 59
def prefixEnd_1733499 : Nat := 4983230072969 + 3 ^ 40 * 1733499 * 2
def baseEnd_1733499 : Nat := 890118201088418410890289

theorem tailTrace_1733499 : CollatzResearch.WordTrace tailWord_1733499 prefixEnd_1733499 890118201088418410890289 := by
  unfold tailWord_1733499
  simp only [CollatzResearch.WordTrace]
  refine ⟨63225902746836655903923551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42150601831224437269282367 63225902746836655903923551)
  ·
    refine ⟨94838854120254983855885327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63225902746836655903923551 94838854120254983855885327)
    ·
      refine ⟨142258281180382475783827991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94838854120254983855885327 142258281180382475783827991)
      ·
        refine ⟨213387421770573713675741987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142258281180382475783827991 213387421770573713675741987)
        ·
          refine ⟨320081132655860570513612981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213387421770573713675741987 320081132655860570513612981)
          ·
            refine ⟨30007606186486928485651217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320081132655860570513612981 30007606186486928485651217)
            ·
              refine ⟨22505704639865196364238413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30007606186486928485651217 22505704639865196364238413)
              ·
                refine ⟨8439639239949448636589405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22505704639865196364238413 8439639239949448636589405)
                ·
                  refine ⟨3164864714981043238721027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8439639239949448636589405 3164864714981043238721027)
                  ·
                    refine ⟨4747297072471564858081541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164864714981043238721027 4747297072471564858081541)
                    ·
                      refine ⟨890118201088418410890289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4747297072471564858081541 890118201088418410890289)
                      ·
                        rfl

theorem cell23_1733499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_1733499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733499 prefixEnd_1733499 := by exact prefixLift 1733499
  have htrace : WordTrace (prefixWord ++ tailWord_1733499) baseStart_1733499 baseEnd_1733499 := by
    simpa [prefixWord, tailWord_1733499, baseEnd_1733499] using wordTrace_append hprefix tailTrace_1733499
  have hstable : (prefixWord ++ tailWord_1733499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733499).length < 2 ^ (prefixWord ++ tailWord_1733499).sum := by decide
  have hdescent : baseEnd_1733499 < baseStart_1733499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733516 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1733516 : Nat := 118140960795 + 1733516 * 2 ^ 59
def prefixEnd_1733516 : Nat := 4983230072969 + 3 ^ 40 * 1733516 * 2
def baseEnd_1733516 : Nat := 890126930259544844377711

theorem tailTrace_1733516 : CollatzResearch.WordTrace tailWord_1733516 prefixEnd_1733516 890126930259544844377711 := by
  unfold tailWord_1733516
  simp only [CollatzResearch.WordTrace]
  refine ⟨31613261393887533903646201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42151015191850045204861601 31613261393887533903646201)
  ·
    refine ⟨23709946045415650427734651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31613261393887533903646201 23709946045415650427734651)
    ·
      refine ⟨35564919068123475641601977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23709946045415650427734651 35564919068123475641601977)
      ·
        refine ⟨26673689301092606731201483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35564919068123475641601977 26673689301092606731201483)
        ·
          refine ⟨40010533951638910096802225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26673689301092606731201483 40010533951638910096802225)
          ·
            refine ⟨30007900463729182572601669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40010533951638910096802225 30007900463729182572601669)
            ·
              refine ⟨5626481336949221732362813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30007900463729182572601669 5626481336949221732362813)
              ·
                refine ⟨2109930501355958149636055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5626481336949221732362813 2109930501355958149636055)
                ·
                  refine ⟨3164895752033937224454083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109930501355958149636055 3164895752033937224454083)
                  ·
                    refine ⟨4747343628050905836681125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164895752033937224454083 4747343628050905836681125)
                    ·
                      refine ⟨890126930259544844377711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4747343628050905836681125 890126930259544844377711)
                      ·
                        rfl

theorem cell23_1733516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1733516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733516 prefixEnd_1733516 := by exact prefixLift 1733516
  have htrace : WordTrace (prefixWord ++ tailWord_1733516) baseStart_1733516 baseEnd_1733516 := by
    simpa [prefixWord, tailWord_1733516, baseEnd_1733516] using wordTrace_append hprefix tailTrace_1733516
  have hstable : (prefixWord ++ tailWord_1733516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733516).length < 2 ^ (prefixWord ++ tailWord_1733516).sum := by decide
  have hdescent : baseEnd_1733516 < baseStart_1733516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733553 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1733553 : Nat := 118140960795 + 1733553 * 2 ^ 59
def prefixEnd_1733553 : Nat := 4983230072969 + 3 ^ 40 * 1733553 * 2
def baseEnd_1733553 : Nat := 890145929043761199615041

theorem tailTrace_1733553 : CollatzResearch.WordTrace tailWord_1733553 prefixEnd_1733553 890145929043761199615041 := by
  unfold tailWord_1733553
  simp only [CollatzResearch.WordTrace]
  refine ⟨63227872288641023126389313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42151914859094015417592875 63227872288641023126389313)
  ·
    refine ⟨47420904216480767344791985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63227872288641023126389313 47420904216480767344791985)
    ·
      refine ⟨35565678162360575508593989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47420904216480767344791985 35565678162360575508593989)
      ·
        refine ⟨6668564655442607907861373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35565678162360575508593989 6668564655442607907861373)
        ·
          refine ⟨2500711745790977965448015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6668564655442607907861373 2500711745790977965448015)
          ·
            refine ⟨3751067618686466948172023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500711745790977965448015 3751067618686466948172023)
            ·
              refine ⟨5626601428029700422258035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751067618686466948172023 5626601428029700422258035)
              ·
                refine ⟨8439902142044550633387053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626601428029700422258035 8439902142044550633387053)
                ·
                  refine ⟨3164963303266706487520145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8439902142044550633387053 3164963303266706487520145)
                  ·
                    refine ⟨2373722477450029865640109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3164963303266706487520145 2373722477450029865640109)
                    ·
                      refine ⟨890145929043761199615041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373722477450029865640109 890145929043761199615041)
                      ·
                        rfl

theorem cell23_1733553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1733553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733553 prefixEnd_1733553 := by exact prefixLift 1733553
  have htrace : WordTrace (prefixWord ++ tailWord_1733553) baseStart_1733553 baseEnd_1733553 := by
    simpa [prefixWord, tailWord_1733553, baseEnd_1733553] using wordTrace_append hprefix tailTrace_1733553
  have hstable : (prefixWord ++ tailWord_1733553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733553).length < 2 ^ (prefixWord ++ tailWord_1733553).sum := by decide
  have hdescent : baseEnd_1733553 < baseStart_1733553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733583 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_1733583 : Nat := 118140960795 + 1733583 * 2 ^ 59
def prefixEnd_1733583 : Nat := 4983230072969 + 3 ^ 40 * 1733583 * 2
def baseEnd_1733583 : Nat := 890161333463396082239903

theorem tailTrace_1733583 : CollatzResearch.WordTrace tailWord_1733583 prefixEnd_1733583 890161333463396082239903 := by
  unfold tailWord_1733583
  simp only [CollatzResearch.WordTrace]
  refine ⟨63228966478532338249981403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42152644319021558833320935 63228966478532338249981403)
  ·
    refine ⟨94843449717798507374972105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63228966478532338249981403 94843449717798507374972105)
    ·
      refine ⟨71132587288348880531229079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94843449717798507374972105 71132587288348880531229079)
      ·
        refine ⟨106698880932523320796843619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71132587288348880531229079 106698880932523320796843619)
        ·
          refine ⟨160048321398784981195265429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106698880932523320796843619 160048321398784981195265429)
          ·
            refine ⟨7502265065568045993528067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160048321398784981195265429 7502265065568045993528067)
            ·
              refine ⟨11253397598352068990292101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502265065568045993528067 11253397598352068990292101)
              ·
                refine ⟨2110012049691012935679769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11253397598352068990292101 2110012049691012935679769)
                ·
                  refine ⟨1582509037268259701759827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2110012049691012935679769 1582509037268259701759827)
                  ·
                    refine ⟨2373763555902389552639741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582509037268259701759827 2373763555902389552639741)
                    ·
                      refine ⟨890161333463396082239903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373763555902389552639741 890161333463396082239903)
                      ·
                        rfl

theorem cell23_1733583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_1733583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733583 prefixEnd_1733583 := by exact prefixLift 1733583
  have htrace : WordTrace (prefixWord ++ tailWord_1733583) baseStart_1733583 baseEnd_1733583 := by
    simpa [prefixWord, tailWord_1733583, baseEnd_1733583] using wordTrace_append hprefix tailTrace_1733583
  have hstable : (prefixWord ++ tailWord_1733583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733583).length < 2 ^ (prefixWord ++ tailWord_1733583).sum := by decide
  have hdescent : baseEnd_1733583 < baseStart_1733583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733586 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1733586 : Nat := 118140960795 + 1733586 * 2 ^ 59
def prefixEnd_1733586 : Nat := 4983230072969 + 3 ^ 40 * 1733586 * 2
def baseEnd_1733586 : Nat := 296720957968453190167463

theorem tailTrace_1733586 : CollatzResearch.WordTrace tailWord_1733586 prefixEnd_1733586 296720957968453190167463 := by
  unfold tailWord_1733586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807268974380367440585153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42152717265014313174893741 15807268974380367440585153)
  ·
    refine ⟨11855451730785275580438865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15807268974380367440585153 11855451730785275580438865)
    ·
      refine ⟨8891588798088956685329149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11855451730785275580438865 8891588798088956685329149)
      ·
        refine ⟨3334345799283358756998431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8891588798088956685329149 3334345799283358756998431)
        ·
          refine ⟨5001518698925038135497647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334345799283358756998431 5001518698925038135497647)
          ·
            refine ⟨7502278048387557203246471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001518698925038135497647 7502278048387557203246471)
            ·
              refine ⟨11253417072581335804869707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502278048387557203246471 11253417072581335804869707)
              ·
                refine ⟨16880125608872003707304561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253417072581335804869707 16880125608872003707304561)
                ·
                  refine ⟨12660094206654002780478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16880125608872003707304561 12660094206654002780478421)
                  ·
                    refine ⟨296720957968453190167463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12660094206654002780478421 296720957968453190167463)
                    ·
                      rfl

theorem cell23_1733586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1733586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733586 prefixEnd_1733586 := by exact prefixLift 1733586
  have htrace : WordTrace (prefixWord ++ tailWord_1733586) baseStart_1733586 baseEnd_1733586 := by
    simpa [prefixWord, tailWord_1733586, baseEnd_1733586] using wordTrace_append hprefix tailTrace_1733586
  have hstable : (prefixWord ++ tailWord_1733586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733586).length < 2 ^ (prefixWord ++ tailWord_1733586).sum := by decide
  have hdescent : baseEnd_1733586 < baseStart_1733586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733593 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 3, 3, 2]
def baseStart_1733593 : Nat := 118140960795 + 1733593 * 2 ^ 59
def prefixEnd_1733593 : Nat := 4983230072969 + 3 ^ 40 * 1733593 * 2
def baseEnd_1733593 : Nat := 890166468269941043114857

theorem tailTrace_1733593 : CollatzResearch.WordTrace tailWord_1733593 prefixEnd_1733593 890166468269941043114857 := by
  unfold tailWord_1733593
  simp only [CollatzResearch.WordTrace]
  refine ⟨63229331208496109957845433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42152887472330739971896955 63229331208496109957845433)
  ·
    refine ⟨47421998406372082468384075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63229331208496109957845433 47421998406372082468384075)
    ·
      refine ⟨71132997609558123702576113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47421998406372082468384075 71132997609558123702576113)
      ·
        refine ⟨53349748207168592776932085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71132997609558123702576113 53349748207168592776932085)
        ·
          refine ⟨5001538894422055572837383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53349748207168592776932085 5001538894422055572837383)
          ·
            refine ⟨7502308341633083359256075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001538894422055572837383 7502308341633083359256075)
            ·
              refine ⟨11253462512449625038884113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502308341633083359256075 11253462512449625038884113)
              ·
                refine ⟨8440096884337218779163085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11253462512449625038884113 8440096884337218779163085)
                ·
                  refine ⟨3165036331626457042186157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8440096884337218779163085 3165036331626457042186157)
                  ·
                    refine ⟨1186888624359921390819809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165036331626457042186157 1186888624359921390819809)
                    ·
                      refine ⟨890166468269941043114857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186888624359921390819809 890166468269941043114857)
                      ·
                        rfl

theorem cell23_1733593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_1733593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733593 prefixEnd_1733593 := by exact prefixLift 1733593
  have htrace : WordTrace (prefixWord ++ tailWord_1733593) baseStart_1733593 baseEnd_1733593 := by
    simpa [prefixWord, tailWord_1733593, baseEnd_1733593] using wordTrace_append hprefix tailTrace_1733593
  have hstable : (prefixWord ++ tailWord_1733593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733593).length < 2 ^ (prefixWord ++ tailWord_1733593).sum := by decide
  have hdescent : baseEnd_1733593 < baseStart_1733593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733621 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1733621 : Nat := 118140960795 + 1733621 * 2 ^ 59
def prefixEnd_1733621 : Nat := 4983230072969 + 3 ^ 40 * 1733621 * 2
def baseEnd_1733621 : Nat := 890180845728266933564729

theorem tailTrace_1733621 : CollatzResearch.WordTrace tailWord_1733621 prefixEnd_1733621 890180845728266933564729 := by
  unfold tailWord_1733621
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230352452394670739864717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42153568301596447159909811 63230352452394670739864717)
  ·
    refine ⟨23711382169648001527449269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63230352452394670739864717 23711382169648001527449269)
    ·
      refine ⟨2222942078404500143198369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23711382169648001527449269 2222942078404500143198369)
      ·
        refine ⟨1667206558803375107398777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222942078404500143198369 1667206558803375107398777)
        ·
          refine ⟨1250404919102531330549083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667206558803375107398777 1250404919102531330549083)
          ·
            refine ⟨1875607378653796995823625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250404919102531330549083 1875607378653796995823625)
            ·
              refine ⟨1406705533990347746867719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875607378653796995823625 1406705533990347746867719)
              ·
                refine ⟨2110058300985521620301579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406705533990347746867719 2110058300985521620301579)
                ·
                  refine ⟨3165087451478282430452369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110058300985521620301579 3165087451478282430452369)
                  ·
                    refine ⟨2373815588608711822839277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3165087451478282430452369 2373815588608711822839277)
                    ·
                      refine ⟨890180845728266933564729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373815588608711822839277 890180845728266933564729)
                      ·
                        rfl

theorem cell23_1733621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1733621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733621 prefixEnd_1733621 := by exact prefixLift 1733621
  have htrace : WordTrace (prefixWord ++ tailWord_1733621) baseStart_1733621 baseEnd_1733621 := by
    simpa [prefixWord, tailWord_1733621, baseEnd_1733621] using wordTrace_append hprefix tailTrace_1733621
  have hstable : (prefixWord ++ tailWord_1733621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733621).length < 2 ^ (prefixWord ++ tailWord_1733621).sum := by decide
  have hdescent : baseEnd_1733621 < baseStart_1733621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733629 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 11]
def baseStart_1733629 : Nat := 118140960795 + 1733629 * 2 ^ 59
def prefixEnd_1733629 : Nat := 4983230072969 + 3 ^ 40 * 1733629 * 2
def baseEnd_1733629 : Nat := 98909439285944766918299

theorem tailTrace_1733629 : CollatzResearch.WordTrace tailWord_1733629 prefixEnd_1733629 98909439285944766918299 := by
  unfold tailWord_1733629
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230644236365688106155941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42153762824243792070770627 63230644236365688106155941)
  ·
    refine ⟨11855745794318566519904239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63230644236365688106155941 11855745794318566519904239)
    ·
      refine ⟨17783618691477849779856359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11855745794318566519904239 17783618691477849779856359)
      ·
        refine ⟨26675428037216774669784539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17783618691477849779856359 26675428037216774669784539)
        ·
          refine ⟨40013142055825162004676809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26675428037216774669784539 40013142055825162004676809)
          ·
            refine ⟨30009856541868871503507607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40013142055825162004676809 30009856541868871503507607)
            ·
              refine ⟨45014784812803307255261411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30009856541868871503507607 45014784812803307255261411)
              ·
                refine ⟨67522177219204960882892117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45014784812803307255261411 67522177219204960882892117)
                ·
                  refine ⟨98909439285944766918299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 67522177219204960882892117 98909439285944766918299)
                  ·
                    rfl

theorem cell23_1733629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_1733629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733629 prefixEnd_1733629 := by exact prefixLift 1733629
  have htrace : WordTrace (prefixWord ++ tailWord_1733629) baseStart_1733629 baseEnd_1733629 := by
    simpa [prefixWord, tailWord_1733629, baseEnd_1733629] using wordTrace_append hprefix tailTrace_1733629
  have hstable : (prefixWord ++ tailWord_1733629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733629).length < 2 ^ (prefixWord ++ tailWord_1733629).sum := by decide
  have hdescent : baseEnd_1733629 < baseStart_1733629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733640 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_1733640 : Nat := 118140960795 + 1733640 * 2 ^ 59
def prefixEnd_1733640 : Nat := 4983230072969 + 3 ^ 40 * 1733640 * 2
def baseEnd_1733640 : Nat := 890190601860702359227141

theorem tailTrace_1733640 : CollatzResearch.WordTrace tailWord_1733640 prefixEnd_1733640 890190601860702359227141 := by
  unfold tailWord_1733640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31615522719662918492403187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42154030292883891323204249 31615522719662918492403187)
  ·
    refine ⟨47423284079494377738604781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31615522719662918492403187 47423284079494377738604781)
    ·
      refine ⟨17783731529810391651976793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47423284079494377738604781 17783731529810391651976793)
      ·
        refine ⟨13337798647357793738982595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17783731529810391651976793 13337798647357793738982595)
        ·
          refine ⟨20006697971036690608473893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337798647357793738982595 20006697971036690608473893)
          ·
            refine ⟨3751255869569379489088855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20006697971036690608473893 3751255869569379489088855)
            ·
              refine ⟨5626883804354069233633283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751255869569379489088855 5626883804354069233633283)
              ·
                refine ⟨8440325706531103850449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626883804354069233633283 8440325706531103850449925)
                ·
                  refine ⟨1582561069974581971959361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8440325706531103850449925 1582561069974581971959361)
                  ·
                    refine ⟨1186920802480936478969521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1582561069974581971959361 1186920802480936478969521)
                    ·
                      refine ⟨890190601860702359227141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186920802480936478969521 890190601860702359227141)
                      ·
                        rfl

theorem cell23_1733640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_1733640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733640 prefixEnd_1733640 := by exact prefixLift 1733640
  have htrace : WordTrace (prefixWord ++ tailWord_1733640) baseStart_1733640 baseEnd_1733640 := by
    simpa [prefixWord, tailWord_1733640, baseEnd_1733640] using wordTrace_append hprefix tailTrace_1733640
  have hstable : (prefixWord ++ tailWord_1733640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733640).length < 2 ^ (prefixWord ++ tailWord_1733640).sum := by decide
  have hdescent : baseEnd_1733640 < baseStart_1733640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733646 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1733646 : Nat := 118140960795 + 1733646 * 2 ^ 59
def prefixEnd_1733646 : Nat := 4983230072969 + 3 ^ 40 * 1733646 * 2
def baseEnd_1733646 : Nat := 98910409193847703972457

theorem tailTrace_1733646 : CollatzResearch.WordTrace tailWord_1733646 prefixEnd_1733646 98910409193847703972457 := by
  unfold tailWord_1733646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903908034663012501190599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42154176184869400006349861 7903908034663012501190599)
  ·
    refine ⟨11855862051994518751785899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7903908034663012501190599 11855862051994518751785899)
    ·
      refine ⟨17783793077991778127678849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11855862051994518751785899 17783793077991778127678849)
      ·
        refine ⟨13337844808493833595759137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17783793077991778127678849 13337844808493833595759137)
        ·
          refine ⟨10003383606370375196819353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13337844808493833595759137 10003383606370375196819353)
          ·
            refine ⟨7502537704777781397614515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10003383606370375196819353 7502537704777781397614515)
            ·
              refine ⟨11253806557166672096421773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502537704777781397614515 11253806557166672096421773)
              ·
                refine ⟨4220177458937502036158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11253806557166672096421773 4220177458937502036158165)
                ·
                  refine ⟨98910409193847703972457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4220177458937502036158165 98910409193847703972457)
                  ·
                    rfl

theorem cell23_1733646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1733646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733646 prefixEnd_1733646 := by exact prefixLift 1733646
  have htrace : WordTrace (prefixWord ++ tailWord_1733646) baseStart_1733646 baseEnd_1733646 := by
    simpa [prefixWord, tailWord_1733646, baseEnd_1733646] using wordTrace_append hprefix tailTrace_1733646
  have hstable : (prefixWord ++ tailWord_1733646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733646).length < 2 ^ (prefixWord ++ tailWord_1733646).sum := by decide
  have hdescent : baseEnd_1733646 < baseStart_1733646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733676 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_1733676 : Nat := 118140960795 + 1733676 * 2 ^ 59
def prefixEnd_1733676 : Nat := 4983230072969 + 3 ^ 40 * 1733676 * 2
def baseEnd_1733676 : Nat := 296736362388088072792325

theorem tailTrace_1733676 : CollatzResearch.WordTrace tailWord_1733676 prefixEnd_1733676 296736362388088072792325 := by
  unfold tailWord_1733676
  simp only [CollatzResearch.WordTrace]
  refine ⟨31616179233597707566558441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42154905644796943422077921 31616179233597707566558441)
  ·
    refine ⟨23712134425198280674918831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31616179233597707566558441 23712134425198280674918831)
    ·
      refine ⟨35568201637797421012378247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23712134425198280674918831 35568201637797421012378247)
      ·
        refine ⟨53352302456696131518567371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35568201637797421012378247 53352302456696131518567371)
        ·
          refine ⟨80028453685044197277851057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53352302456696131518567371 80028453685044197277851057)
          ·
            refine ⟨60021340263783147958388293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80028453685044197277851057 60021340263783147958388293)
            ·
              refine ⟨11254001299459340242197805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60021340263783147958388293 11254001299459340242197805)
              ·
                refine ⟨4220250487297252590824177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11254001299459340242197805 4220250487297252590824177)
                ·
                  refine ⟨3165187865472939443118133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220250487297252590824177 3165187865472939443118133)
                  ·
                    refine ⟨296736362388088072792325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3165187865472939443118133 296736362388088072792325)
                    ·
                      rfl

theorem cell23_1733676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_1733676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733676 prefixEnd_1733676 := by exact prefixLift 1733676
  have htrace : WordTrace (prefixWord ++ tailWord_1733676) baseStart_1733676 baseEnd_1733676 := by
    simpa [prefixWord, tailWord_1733676, baseEnd_1733676] using wordTrace_append hprefix tailTrace_1733676
  have hstable : (prefixWord ++ tailWord_1733676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733676).length < 2 ^ (prefixWord ++ tailWord_1733676).sum := by decide
  have hdescent : baseEnd_1733676 < baseStart_1733676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_1733679 : Nat := 118140960795 + 1733679 * 2 ^ 59
def prefixEnd_1733679 : Nat := 4983230072969 + 3 ^ 40 * 1733679 * 2
def baseEnd_1733679 : Nat := 890210627606227706639461

theorem tailTrace_1733679 : CollatzResearch.WordTrace tailWord_1733679 prefixEnd_1733679 890210627606227706639461 := by
  unfold tailWord_1733679
  simp only [CollatzResearch.WordTrace]
  refine ⟨63232467886184546645476091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42154978590789697763650727 63232467886184546645476091)
  ·
    refine ⟨94848701829276819968214137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63232467886184546645476091 94848701829276819968214137)
    ·
      refine ⟨71136526371957614976160603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94848701829276819968214137 71136526371957614976160603)
      ·
        refine ⟨106704789557936422464240905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71136526371957614976160603 106704789557936422464240905)
        ·
          refine ⟨80028592168452316848180679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106704789557936422464240905 80028592168452316848180679)
          ·
            refine ⟨120042888252678475272271019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80028592168452316848180679 120042888252678475272271019)
            ·
              refine ⟨180064332379017712908406529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120042888252678475272271019 180064332379017712908406529)
              ·
                refine ⟨135048249284263284681304897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180064332379017712908406529 135048249284263284681304897)
                ·
                  refine ⟨101286186963197463510978673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135048249284263284681304897 101286186963197463510978673)
                  ·
                    refine ⟨75964640222398097633234005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101286186963197463510978673 75964640222398097633234005)
                    ·
                      refine ⟨890210627606227706639461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75964640222398097633234005 890210627606227706639461)
                      ·
                        rfl

theorem cell23_1733679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_1733679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733679 prefixEnd_1733679 := by exact prefixLift 1733679
  have htrace : WordTrace (prefixWord ++ tailWord_1733679) baseStart_1733679 baseEnd_1733679 := by
    simpa [prefixWord, tailWord_1733679, baseEnd_1733679] using wordTrace_append hprefix tailTrace_1733679
  have hstable : (prefixWord ++ tailWord_1733679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733679).length < 2 ^ (prefixWord ++ tailWord_1733679).sum := by decide
  have hdescent : baseEnd_1733679 < baseStart_1733679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733693 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1733693 : Nat := 118140960795 + 1733693 * 2 ^ 59
def prefixEnd_1733693 : Nat := 4983230072969 + 3 ^ 40 * 1733693 * 2
def baseEnd_1733693 : Nat := 296739272111796883954799

theorem tailTrace_1733693 : CollatzResearch.WordTrace tailWord_1733693 prefixEnd_1733693 296739272111796883954799 := by
  unfold tailWord_1733693
  simp only [CollatzResearch.WordTrace]
  refine ⟨63232978508133827036485733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42155319005422551357657155 63232978508133827036485733)
  ·
    refine ⟨11856183470275092569341075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63232978508133827036485733 11856183470275092569341075)
    ·
      refine ⟨17784275205412638854011613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856183470275092569341075 17784275205412638854011613)
      ·
        refine ⟨6669103202029739570254355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17784275205412638854011613 6669103202029739570254355)
        ·
          refine ⟨10003654803044609355381533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669103202029739570254355 10003654803044609355381533)
          ·
            refine ⟨3751370551141728508268075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10003654803044609355381533 3751370551141728508268075)
            ·
              refine ⟨5627055826712592762402113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751370551141728508268075 5627055826712592762402113)
              ·
                refine ⟨4220291870034444571801585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627055826712592762402113 4220291870034444571801585)
                ·
                  refine ⟨3165218902525833428851189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220291870034444571801585 3165218902525833428851189)
                  ·
                    refine ⟨296739272111796883954799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3165218902525833428851189 296739272111796883954799)
                    ·
                      rfl

theorem cell23_1733693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1733693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733693 prefixEnd_1733693 := by exact prefixLift 1733693
  have htrace : WordTrace (prefixWord ++ tailWord_1733693) baseStart_1733693 baseEnd_1733693 := by
    simpa [prefixWord, tailWord_1733693, baseEnd_1733693] using wordTrace_append hprefix tailTrace_1733693
  have hstable : (prefixWord ++ tailWord_1733693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733693).length < 2 ^ (prefixWord ++ tailWord_1733693).sum := by decide
  have hdescent : baseEnd_1733693 < baseStart_1733693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733697 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 5]
def baseStart_1733697 : Nat := 118140960795 + 1733697 * 2 ^ 59
def prefixEnd_1733697 : Nat := 4983230072969 + 3 ^ 40 * 1733697 * 2
def baseEnd_1733697 : Nat := 98913318917556515134931

theorem tailTrace_1733697 : CollatzResearch.WordTrace tailWord_1733697 prefixEnd_1733697 98913318917556515134931 := by
  unfold tailWord_1733697
  simp only [CollatzResearch.WordTrace]
  refine ⟨63233124400119335719631345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42155416266746223813087563 63233124400119335719631345)
  ·
    refine ⟨47424843300089501789723509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63233124400119335719631345 47424843300089501789723509)
    ·
      refine ⟨4446079059383390792786579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47424843300089501789723509 4446079059383390792786579)
      ·
        refine ⟨6669118589075086189179869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446079059383390792786579 6669118589075086189179869)
        ·
          refine ⟨2500919470903157320942451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6669118589075086189179869 2500919470903157320942451)
          ·
            refine ⟨3751379206354735981413677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500919470903157320942451 3751379206354735981413677)
            ·
              refine ⟨1406767202383025993030129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751379206354735981413677 1406767202383025993030129)
              ·
                refine ⟨1055075401787269494772597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406767202383025993030129 1055075401787269494772597)
                ·
                  refine ⟨98913318917556515134931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1055075401787269494772597 98913318917556515134931)
                  ·
                    rfl

theorem cell23_1733697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 5].length) (baseStart_1733697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733697 prefixEnd_1733697 := by exact prefixLift 1733697
  have htrace : WordTrace (prefixWord ++ tailWord_1733697) baseStart_1733697 baseEnd_1733697 := by
    simpa [prefixWord, tailWord_1733697, baseEnd_1733697] using wordTrace_append hprefix tailTrace_1733697
  have hstable : (prefixWord ++ tailWord_1733697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733697).length < 2 ^ (prefixWord ++ tailWord_1733697).sum := by decide
  have hdescent : baseEnd_1733697 < baseStart_1733697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733713 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_1733713 : Nat := 118140960795 + 1733713 * 2 ^ 59
def prefixEnd_1733713 : Nat := 4983230072969 + 3 ^ 40 * 1733713 * 2
def baseEnd_1733713 : Nat := 890228085948480573614305

theorem tailTrace_1733713 : CollatzResearch.WordTrace tailWord_1733713 prefixEnd_1733713 890228085948480573614305 := by
  unfold tailWord_1733713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63233707968061370452213793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42155805312040913634809195 63233707968061370452213793)
  ·
    refine ⟨47425280976046027839160345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63233707968061370452213793 47425280976046027839160345)
    ·
      refine ⟨35568960732034520879370259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47425280976046027839160345 35568960732034520879370259)
      ·
        refine ⟨53353441098051781319055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35568960732034520879370259 53353441098051781319055389)
        ·
          refine ⟨20007540411769417994645771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53353441098051781319055389 20007540411769417994645771)
          ·
            refine ⟨30011310617654126991968657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20007540411769417994645771 30011310617654126991968657)
            ·
              refine ⟨22508482963240595243976493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30011310617654126991968657 22508482963240595243976493)
              ·
                refine ⟨8440681111215223216491185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22508482963240595243976493 8440681111215223216491185)
                ·
                  refine ⟨6330510833411417412368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8440681111215223216491185 6330510833411417412368389)
                  ·
                    refine ⟨1186970781264640764819073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6330510833411417412368389 1186970781264640764819073)
                    ·
                      refine ⟨890228085948480573614305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186970781264640764819073 890228085948480573614305)
                      ·
                        rfl

theorem cell23_1733713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_1733713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733713 prefixEnd_1733713 := by exact prefixLift 1733713
  have htrace : WordTrace (prefixWord ++ tailWord_1733713) baseStart_1733713 baseEnd_1733713 := by
    simpa [prefixWord, tailWord_1733713, baseEnd_1733713] using wordTrace_append hprefix tailTrace_1733713
  have hstable : (prefixWord ++ tailWord_1733713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733713).length < 2 ^ (prefixWord ++ tailWord_1733713).sum := by decide
  have hdescent : baseEnd_1733713 < baseStart_1733713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733730 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1733730 : Nat := 118140960795 + 1733730 * 2 ^ 59
def prefixEnd_1733730 : Nat := 4983230072969 + 3 ^ 40 * 1733730 * 2
def baseEnd_1733730 : Nat := 890236815119607007101727

theorem tailTrace_1733730 : CollatzResearch.WordTrace tailWord_1733730 prefixEnd_1733730 890236815119607007101727 := by
  unfold tailWord_1733730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808582002249945588895661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42156218672666521570388429 15808582002249945588895661)
  ·
    refine ⟨5928218250843729595835873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15808582002249945588895661 5928218250843729595835873)
    ·
      refine ⟨4446163688132797196876905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5928218250843729595835873 4446163688132797196876905)
      ·
        refine ⟨3334622766099597897657679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4446163688132797196876905 3334622766099597897657679)
        ·
          refine ⟨5001934149149396846486519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334622766099597897657679 5001934149149396846486519)
          ·
            refine ⟨7502901223724095269729779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001934149149396846486519 7502901223724095269729779)
            ·
              refine ⟨11254351835586142904594669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502901223724095269729779 11254351835586142904594669)
              ·
                refine ⟨4220381938344803589223001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11254351835586142904594669 4220381938344803589223001)
                ·
                  refine ⟨3165286453758602691917251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220381938344803589223001 3165286453758602691917251)
                  ·
                    refine ⟨4747929680637904037875877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3165286453758602691917251 4747929680637904037875877)
                    ·
                      refine ⟨890236815119607007101727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4747929680637904037875877 890236815119607007101727)
                      ·
                        rfl

theorem cell23_1733730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1733730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733730 prefixEnd_1733730 := by exact prefixLift 1733730
  have htrace : WordTrace (prefixWord ++ tailWord_1733730) baseStart_1733730 baseEnd_1733730 := by
    simpa [prefixWord, tailWord_1733730, baseEnd_1733730] using wordTrace_append hprefix tailTrace_1733730
  have hstable : (prefixWord ++ tailWord_1733730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733730).length < 2 ^ (prefixWord ++ tailWord_1733730).sum := by decide
  have hdescent : baseEnd_1733730 < baseStart_1733730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733740 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_1733740 : Nat := 118140960795 + 1733740 * 2 ^ 59
def prefixEnd_1733740 : Nat := 4983230072969 + 3 ^ 40 * 1733740 * 2
def baseEnd_1733740 : Nat := 296747316642050655992227

theorem tailTrace_1733740 : CollatzResearch.WordTrace tailWord_1733740 prefixEnd_1733740 296747316642050655992227 := by
  unfold tailWord_1733740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31617346369481777031723337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42156461825975702708964449 31617346369481777031723337)
  ·
    refine ⟨23713009777111332773792503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31617346369481777031723337 23713009777111332773792503)
    ·
      refine ⟨35569514665666999160688755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23713009777111332773792503 35569514665666999160688755)
      ·
        refine ⟨53354271998500498741033133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35569514665666999160688755 53354271998500498741033133)
        ·
          refine ⟨20007851999437687027887425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53354271998500498741033133 20007851999437687027887425)
          ·
            refine ⟨15005888999578265270915569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20007851999437687027887425 15005888999578265270915569)
            ·
              refine ⟨11254416749683698953186677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15005888999578265270915569 11254416749683698953186677)
              ·
                refine ⟨1055101570282846776861251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11254416749683698953186677 1055101570282846776861251)
                ·
                  refine ⟨1582652355424270165291877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055101570282846776861251 1582652355424270165291877)
                  ·
                    refine ⟨296747316642050655992227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1582652355424270165291877 296747316642050655992227)
                    ·
                      rfl

theorem cell23_1733740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_1733740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733740 prefixEnd_1733740 := by exact prefixLift 1733740
  have htrace : WordTrace (prefixWord ++ tailWord_1733740) baseStart_1733740 baseEnd_1733740 := by
    simpa [prefixWord, tailWord_1733740, baseEnd_1733740] using wordTrace_append hprefix tailTrace_1733740
  have hstable : (prefixWord ++ tailWord_1733740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733740).length < 2 ^ (prefixWord ++ tailWord_1733740).sum := by decide
  have hdescent : baseEnd_1733740 < baseStart_1733740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733750 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1733750 : Nat := 118140960795 + 1733750 * 2 ^ 59
def prefixEnd_1733750 : Nat := 4983230072969 + 3 ^ 40 * 1733750 * 2
def baseEnd_1733750 : Nat := 890247084732696928851635

theorem tailTrace_1733750 : CollatzResearch.WordTrace tailWord_1733750 prefixEnd_1733750 890247084732696928851635 := by
  unfold tailWord_1733750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952191091807957860706919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42156704979284883847540469 3952191091807957860706919)
  ·
    refine ⟨5928286637711936791060379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3952191091807957860706919 5928286637711936791060379)
    ·
      refine ⟨8892429956567905186590569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928286637711936791060379 8892429956567905186590569)
      ·
        refine ⟨6669322467425928889942927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8892429956567905186590569 6669322467425928889942927)
        ·
          refine ⟨10003983701138893334914391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669322467425928889942927 10003983701138893334914391)
          ·
            refine ⟨15005975551708340002371587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10003983701138893334914391 15005975551708340002371587)
            ·
              refine ⟨22508963327562510003557381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15005975551708340002371587 22508963327562510003557381)
              ·
                refine ⟨4220430623917970625667009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22508963327562510003557381 4220430623917970625667009)
                ·
                  refine ⟨3165322967938477969250257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220430623917970625667009 3165322967938477969250257)
                  ·
                    refine ⟨2373992225953858476937693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3165322967938477969250257 2373992225953858476937693)
                    ·
                      refine ⟨890247084732696928851635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373992225953858476937693 890247084732696928851635)
                      ·
                        rfl

theorem cell23_1733750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1733750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733750 prefixEnd_1733750 := by exact prefixLift 1733750
  have htrace : WordTrace (prefixWord ++ tailWord_1733750) baseStart_1733750 baseEnd_1733750 := by
    simpa [prefixWord, tailWord_1733750, baseEnd_1733750] using wordTrace_append hprefix tailTrace_1733750
  have hstable : (prefixWord ++ tailWord_1733750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733750).length < 2 ^ (prefixWord ++ tailWord_1733750).sum := by decide
  have hdescent : baseEnd_1733750 < baseStart_1733750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733756 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1733756 : Nat := 118140960795 + 1733756 * 2 ^ 59
def prefixEnd_1733756 : Nat := 4983230072969 + 3 ^ 40 * 1733756 * 2
def baseEnd_1733756 : Nat := 890250165616623905376607

theorem tailTrace_1733756 : CollatzResearch.WordTrace tailWord_1733756 prefixEnd_1733756 890250165616623905376607 := by
  unfold tailWord_1733756
  simp only [CollatzResearch.WordTrace]
  refine ⟨31617638153452794398014561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42156850871270392530686081 31617638153452794398014561)
  ·
    refine ⟨23713228615089595798510921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31617638153452794398014561 23713228615089595798510921)
    ·
      refine ⟨17784921461317196848883191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23713228615089595798510921 17784921461317196848883191)
      ·
        refine ⟨26677382191975795273324787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784921461317196848883191 26677382191975795273324787)
        ·
          refine ⟨40016073287963692909987181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26677382191975795273324787 40016073287963692909987181)
          ·
            refine ⟨15006027482986384841245193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40016073287963692909987181 15006027482986384841245193)
            ·
              refine ⟨11254520612239788630933895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15006027482986384841245193 11254520612239788630933895)
              ·
                refine ⟨16881780918359682946400843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11254520612239788630933895 16881780918359682946400843)
                ·
                  refine ⟨25322671377539524419601265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16881780918359682946400843 25322671377539524419601265)
                  ·
                    refine ⟨18992003533154643314700949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25322671377539524419601265 18992003533154643314700949)
                    ·
                      refine ⟨890250165616623905376607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18992003533154643314700949 890250165616623905376607)
                      ·
                        rfl

theorem cell23_1733756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1733756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733756 prefixEnd_1733756 := by exact prefixLift 1733756
  have htrace : WordTrace (prefixWord ++ tailWord_1733756) baseStart_1733756 baseEnd_1733756 := by
    simpa [prefixWord, tailWord_1733756, baseEnd_1733756] using wordTrace_append hprefix tailTrace_1733756
  have hstable : (prefixWord ++ tailWord_1733756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733756).length < 2 ^ (prefixWord ++ tailWord_1733756).sum := by decide
  have hdescent : baseEnd_1733756 < baseStart_1733756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733783 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 3, 5]
def baseStart_1733783 : Nat := 118140960795 + 1733783 * 2 ^ 59
def prefixEnd_1733783 : Nat := 4983230072969 + 3 ^ 40 * 1733783 * 2
def baseEnd_1733783 : Nat := 296754676531431766579661

theorem tailTrace_1733783 : CollatzResearch.WordTrace tailWord_1733783 prefixEnd_1733783 296754676531431766579661 := by
  unfold tailWord_1733783
  simp only [CollatzResearch.WordTrace]
  refine ⟨63236261077807772407262003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42157507385205181604841335 63236261077807772407262003)
  ·
    refine ⟨94854391616711658610893005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63236261077807772407262003 94854391616711658610893005)
    ·
      refine ⟨35570396856266871979084877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94854391616711658610893005 35570396856266871979084877)
      ·
        refine ⟨13338898821100076992156829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35570396856266871979084877 13338898821100076992156829)
        ·
          refine ⟨5002087057912528872058811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13338898821100076992156829 5002087057912528872058811)
          ·
            refine ⟨7503130586868793308088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002087057912528872058811 7503130586868793308088217)
            ·
              refine ⟨5627347940151594981066163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7503130586868793308088217 5627347940151594981066163)
              ·
                refine ⟨8441021910227392471599245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627347940151594981066163 8441021910227392471599245)
                ·
                  refine ⟨3165383216335272176849717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8441021910227392471599245 3165383216335272176849717)
                  ·
                    refine ⟨296754676531431766579661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3165383216335272176849717 296754676531431766579661)
                    ·
                      rfl

theorem cell23_1733783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_1733783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733783 prefixEnd_1733783 := by exact prefixLift 1733783
  have htrace : WordTrace (prefixWord ++ tailWord_1733783) baseStart_1733783 baseEnd_1733783 := by
    simpa [prefixWord, tailWord_1733783, baseEnd_1733783] using wordTrace_append hprefix tailTrace_1733783
  have hstable : (prefixWord ++ tailWord_1733783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733783).length < 2 ^ (prefixWord ++ tailWord_1733783).sum := by decide
  have hdescent : baseEnd_1733783 < baseStart_1733783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733797 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_1733797 : Nat := 118140960795 + 1733797 * 2 ^ 59
def prefixEnd_1733797 : Nat := 4983230072969 + 3 ^ 40 * 1733797 * 2
def baseEnd_1733797 : Nat := 890271218323458244963919

theorem tailTrace_1733797 : CollatzResearch.WordTrace tailWord_1733797 prefixEnd_1733797 890271218323458244963919 := by
  unfold tailWord_1733797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63236771699757052798271645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42157847799838035198847763 63236771699757052798271645)
  ·
    refine ⟨23713789387408894799351867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63236771699757052798271645 23713789387408894799351867)
    ·
      refine ⟨35570684081113342199027801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23713789387408894799351867 35570684081113342199027801)
      ·
        refine ⟨26678013060835006649270851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35570684081113342199027801 26678013060835006649270851)
        ·
          refine ⟨40017019591252509973906277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26678013060835006649270851 40017019591252509973906277)
          ·
            refine ⟨7503191173359845620107427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40017019591252509973906277 7503191173359845620107427)
            ·
              refine ⟨11254786760039768430161141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503191173359845620107427 11254786760039768430161141)
              ·
                refine ⟨1055136258753728290327607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11254786760039768430161141 1055136258753728290327607)
                ·
                  refine ⟨1582704388130592435491411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055136258753728290327607 1582704388130592435491411)
                  ·
                    refine ⟨2374056582195888653237117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582704388130592435491411 2374056582195888653237117)
                    ·
                      refine ⟨890271218323458244963919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374056582195888653237117 890271218323458244963919)
                      ·
                        rfl

theorem cell23_1733797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_1733797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733797 prefixEnd_1733797 := by exact prefixLift 1733797
  have htrace : WordTrace (prefixWord ++ tailWord_1733797) baseStart_1733797 baseEnd_1733797 := by
    simpa [prefixWord, tailWord_1733797, baseEnd_1733797] using wordTrace_append hprefix tailTrace_1733797
  have hstable : (prefixWord ++ tailWord_1733797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733797).length < 2 ^ (prefixWord ++ tailWord_1733797).sum := by decide
  have hdescent : baseEnd_1733797 < baseStart_1733797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733823 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1733823 : Nat := 118140960795 + 1733823 * 2 ^ 59
def prefixEnd_1733823 : Nat := 4983230072969 + 3 ^ 40 * 1733823 * 2
def baseEnd_1733823 : Nat := 890284568820475143238799

theorem tailTrace_1733823 : CollatzResearch.WordTrace tailWord_1733823 prefixEnd_1733823 890284568820475143238799 := by
  unfold tailWord_1733823
  simp only [CollatzResearch.WordTrace]
  refine ⟨63237719997662859238718123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42158479998441906159145415 63237719997662859238718123)
  ·
    refine ⟨94856579996494288858077185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63237719997662859238718123 94856579996494288858077185)
    ·
      refine ⟨71142434997370716643557889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94856579996494288858077185 71142434997370716643557889)
      ·
        refine ⟨53356826248028037482668417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71142434997370716643557889 53356826248028037482668417)
        ·
          refine ⟨40017619686021028112001313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53356826248028037482668417 40017619686021028112001313)
          ·
            refine ⟨30013214764515771084000985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40017619686021028112001313 30013214764515771084000985)
            ·
              refine ⟨22509911073386828313000739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30013214764515771084000985 22509911073386828313000739)
              ·
                refine ⟨33764866610080242469501109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22509911073386828313000739 33764866610080242469501109)
                ·
                  refine ⟨3165456244695022731515729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33764866610080242469501109 3165456244695022731515729)
                  ·
                    refine ⟨2374092183521267048636797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3165456244695022731515729 2374092183521267048636797)
                    ·
                      refine ⟨890284568820475143238799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374092183521267048636797 890284568820475143238799)
                      ·
                        rfl

theorem cell23_1733823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1733823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733823 prefixEnd_1733823 := by exact prefixLift 1733823
  have htrace : WordTrace (prefixWord ++ tailWord_1733823) baseStart_1733823 baseEnd_1733823 := by
    simpa [prefixWord, tailWord_1733823, baseEnd_1733823] using wordTrace_append hprefix tailTrace_1733823
  have hstable : (prefixWord ++ tailWord_1733823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733823).length < 2 ^ (prefixWord ++ tailWord_1733823).sum := by decide
  have hdescent : baseEnd_1733823 < baseStart_1733823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733871 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 3, 2, 2]
def baseStart_1733871 : Nat := 118140960795 + 1733871 * 2 ^ 59
def prefixEnd_1733871 : Nat := 4983230072969 + 3 ^ 40 * 1733871 * 2
def baseEnd_1733871 : Nat := 890309215891890955438579

theorem tailTrace_1733871 : CollatzResearch.WordTrace tailWord_1733871 prefixEnd_1733871 890309215891890955438579 := by
  unfold tailWord_1733871
  simp only [CollatzResearch.WordTrace]
  refine ⟨63239470701488963436465467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42159647134325975624310311 63239470701488963436465467)
  ·
    refine ⟨94859206052233445154698201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63239470701488963436465467 94859206052233445154698201)
    ·
      refine ⟨71144404539175083866023651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94859206052233445154698201 71144404539175083866023651)
      ·
        refine ⟨106716606808762625799035477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71144404539175083866023651 106716606808762625799035477)
        ·
          refine ⟨1250585236040187021082447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 106716606808762625799035477 1250585236040187021082447)
          ·
            refine ⟨1875877854060280531623671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250585236040187021082447 1875877854060280531623671)
            ·
              refine ⟨2813816781090420797435507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875877854060280531623671 2813816781090420797435507)
              ·
                refine ⟨4220725171635631196153261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813816781090420797435507 4220725171635631196153261)
                ·
                  refine ⟨1582771939363361698557473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4220725171635631196153261 1582771939363361698557473)
                  ·
                    refine ⟨1187078954522521273918105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1582771939363361698557473 1187078954522521273918105)
                    ·
                      refine ⟨890309215891890955438579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187078954522521273918105 890309215891890955438579)
                      ·
                        rfl

theorem cell23_1733871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 2, 2].length) (baseStart_1733871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733871 prefixEnd_1733871 := by exact prefixLift 1733871
  have htrace : WordTrace (prefixWord ++ tailWord_1733871) baseStart_1733871 baseEnd_1733871 := by
    simpa [prefixWord, tailWord_1733871, baseEnd_1733871] using wordTrace_append hprefix tailTrace_1733871
  have hstable : (prefixWord ++ tailWord_1733871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733871).length < 2 ^ (prefixWord ++ tailWord_1733871).sum := by decide
  have hdescent : baseEnd_1733871 < baseStart_1733871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733887 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_1733887 : Nat := 118140960795 + 1733887 * 2 ^ 59
def prefixEnd_1733887 : Nat := 4983230072969 + 3 ^ 40 * 1733887 * 2
def baseEnd_1733887 : Nat := 890317431582362892838505

theorem tailTrace_1733887 : CollatzResearch.WordTrace tailWord_1733887 prefixEnd_1733887 890317431582362892838505 := by
  unfold tailWord_1733887
  simp only [CollatzResearch.WordTrace]
  refine ⟨63240054269430998169047915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42160036179620665446031943 63240054269430998169047915)
  ·
    refine ⟨94860081404146497253571873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63240054269430998169047915 94860081404146497253571873)
    ·
      refine ⟨71145061053109872940178905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94860081404146497253571873 71145061053109872940178905)
      ·
        refine ⟨53358795789832404705134179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71145061053109872940178905 53358795789832404705134179)
        ·
          refine ⟨80038193684748607057701269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53358795789832404705134179 80038193684748607057701269)
          ·
            refine ⟨3751790328972590955829747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80038193684748607057701269 3751790328972590955829747)
            ·
              refine ⟨5627685493458886433744621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751790328972590955829747 5627685493458886433744621)
              ·
                refine ⟨2110382060047082412654233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5627685493458886433744621 2110382060047082412654233)
                ·
                  refine ⟨1582786545035311809490675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2110382060047082412654233 1582786545035311809490675)
                  ·
                    refine ⟨2374179817552967714236013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582786545035311809490675 2374179817552967714236013)
                    ·
                      refine ⟨890317431582362892838505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374179817552967714236013 890317431582362892838505)
                      ·
                        rfl

theorem cell23_1733887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_1733887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733887 prefixEnd_1733887 := by exact prefixLift 1733887
  have htrace : WordTrace (prefixWord ++ tailWord_1733887) baseStart_1733887 baseEnd_1733887 := by
    simpa [prefixWord, tailWord_1733887, baseEnd_1733887] using wordTrace_append hprefix tailTrace_1733887
  have hstable : (prefixWord ++ tailWord_1733887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733887).length < 2 ^ (prefixWord ++ tailWord_1733887).sum := by decide
  have hdescent : baseEnd_1733887 < baseStart_1733887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733913 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_1733913 : Nat := 118140960795 + 1733913 * 2 ^ 59
def prefixEnd_1733913 : Nat := 4983230072969 + 3 ^ 40 * 1733913 * 2
def baseEnd_1733913 : Nat := 890330782079379791113385

theorem tailTrace_1733913 : CollatzResearch.WordTrace tailWord_1733913 prefixEnd_1733913 890330782079379791113385 := by
  unfold tailWord_1733913
  simp only [CollatzResearch.WordTrace]
  refine ⟨63241002567336804609494393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42160668378224536406329595 63241002567336804609494393)
  ·
    refine ⟨47430751925502603457120795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63241002567336804609494393 47430751925502603457120795)
    ·
      refine ⟨71146127888253905185681193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47430751925502603457120795 71146127888253905185681193)
      ·
        refine ⟨53359595916190428889260895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71146127888253905185681193 53359595916190428889260895)
        ·
          refine ⟨80039393874285643333891343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53359595916190428889260895 80039393874285643333891343)
          ·
            refine ⟨120059090811428465000837015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80039393874285643333891343 120059090811428465000837015)
            ·
              refine ⟨180088636217142697501255523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120059090811428465000837015 180088636217142697501255523)
              ·
                refine ⟨270132954325714046251883285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180088636217142697501255523 270132954325714046251883285)
                ·
                  refine ⟨12662482234017845918057029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270132954325714046251883285 12662482234017845918057029)
                  ·
                    refine ⟨2374215418878346109635693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12662482234017845918057029 2374215418878346109635693)
                    ·
                      refine ⟨890330782079379791113385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374215418878346109635693 890330782079379791113385)
                      ·
                        rfl

theorem cell23_1733913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_1733913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733913 prefixEnd_1733913 := by exact prefixLift 1733913
  have htrace : WordTrace (prefixWord ++ tailWord_1733913) baseStart_1733913 baseEnd_1733913 := by
    simpa [prefixWord, tailWord_1733913, baseEnd_1733913] using wordTrace_append hprefix tailTrace_1733913
  have hstable : (prefixWord ++ tailWord_1733913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733913).length < 2 ^ (prefixWord ++ tailWord_1733913).sum := by decide
  have hdescent : baseEnd_1733913 < baseStart_1733913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733950 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1733950 : Nat := 118140960795 + 1733950 * 2 ^ 59
def prefixEnd_1733950 : Nat := 4983230072969 + 3 ^ 40 * 1733950 * 2
def baseEnd_1733950 : Nat := 98927753429288460705635

theorem tailTrace_1733950 : CollatzResearch.WordTrace tailWord_1733950 prefixEnd_1733950 98927753429288460705635 := by
  unfold tailWord_1733950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905294008525344991073913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42161568045468506619060869 7905294008525344991073913)
  ·
    refine ⟨5928970506394008743305435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7905294008525344991073913 5928970506394008743305435)
    ·
      refine ⟨8893455759591013114958153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928970506394008743305435 8893455759591013114958153)
      ·
        refine ⟨6670091819693259836218615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8893455759591013114958153 6670091819693259836218615)
        ·
          refine ⟨10005137729539889754327923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670091819693259836218615 10005137729539889754327923)
          ·
            refine ⟨15007706594309834631491885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005137729539889754327923 15007706594309834631491885)
            ·
              refine ⟨5627889972866187986809457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15007706594309834631491885 5627889972866187986809457)
              ·
                refine ⟨4220917479649640990107093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627889972866187986809457 4220917479649640990107093)
                ·
                  refine ⟨98927753429288460705635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4220917479649640990107093 98927753429288460705635)
                  ·
                    rfl

theorem cell23_1733950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1733950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733950 prefixEnd_1733950 := by exact prefixLift 1733950
  have htrace : WordTrace (prefixWord ++ tailWord_1733950) baseStart_1733950 baseEnd_1733950 := by
    simpa [prefixWord, tailWord_1733950, baseEnd_1733950] using wordTrace_append hprefix tailTrace_1733950
  have hstable : (prefixWord ++ tailWord_1733950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733950).length < 2 ^ (prefixWord ++ tailWord_1733950).sum := by decide
  have hdescent : baseEnd_1733950 < baseStart_1733950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733965 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1733965 : Nat := 118140960795 + 1733965 * 2 ^ 59
def prefixEnd_1733965 : Nat := 4983230072969 + 3 ^ 40 * 1733965 * 2
def baseEnd_1733965 : Nat := 890357483073413587663147

theorem tailTrace_1733965 : CollatzResearch.WordTrace tailWord_1733965 prefixEnd_1733965 890357483073413587663147 := by
  unfold tailWord_1733965
  simp only [CollatzResearch.WordTrace]
  refine ⟨63242899163148417490387349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42161932775432278326924899 63242899163148417490387349)
  ·
    refine ⟨2964510898272582069861907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63242899163148417490387349 2964510898272582069861907)
    ·
      refine ⟨4446766347408873104792861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964510898272582069861907 4446766347408873104792861)
      ·
        refine ⟨1667537380278327414297323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4446766347408873104792861 1667537380278327414297323)
        ·
          refine ⟨2501306070417491121445985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667537380278327414297323 2501306070417491121445985)
          ·
            refine ⟨1875979552813118341084489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501306070417491121445985 1875979552813118341084489)
            ·
              refine ⟨1406984664609838755813367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875979552813118341084489 1406984664609838755813367)
              ·
                refine ⟨2110476996914758133720051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406984664609838755813367 2110476996914758133720051)
                ·
                  refine ⟨3165715495372137200580077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110476996914758133720051 3165715495372137200580077)
                  ·
                    refine ⟨1187143310764551450217529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165715495372137200580077 1187143310764551450217529)
                    ·
                      refine ⟨890357483073413587663147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187143310764551450217529 890357483073413587663147)
                      ·
                        rfl

theorem cell23_1733965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1733965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733965 prefixEnd_1733965 := by exact prefixLift 1733965
  have htrace : WordTrace (prefixWord ++ tailWord_1733965) baseStart_1733965 baseEnd_1733965 := by
    simpa [prefixWord, tailWord_1733965, baseEnd_1733965] using wordTrace_append hprefix tailTrace_1733965
  have hstable : (prefixWord ++ tailWord_1733965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733965).length < 2 ^ (prefixWord ++ tailWord_1733965).sum := by decide
  have hdescent : baseEnd_1733965 < baseStart_1733965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734067 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 3]
def baseStart_1734067 : Nat := 118140960795 + 1734067 * 2 ^ 59
def prefixEnd_1734067 : Nat := 4983230072969 + 3 ^ 40 * 1734067 * 2
def baseEnd_1734067 : Nat := 890409858100172188587677

theorem tailTrace_1734067 : CollatzResearch.WordTrace tailWord_1734067 prefixEnd_1734067 890409858100172188587677 := by
  unfold tailWord_1734067
  simp only [CollatzResearch.WordTrace]
  refine ⟨63246619408778888910600455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42164412939185925940400303 63246619408778888910600455)
  ·
    refine ⟨94869929113168333365900683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63246619408778888910600455 94869929113168333365900683)
    ·
      refine ⟨142304893669752500048851025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94869929113168333365900683 142304893669752500048851025)
      ·
        refine ⟨106728670252314375036638269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142304893669752500048851025 106728670252314375036638269)
        ·
          refine ⟨40023251344617890638739351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106728670252314375036638269 40023251344617890638739351)
          ·
            refine ⟨60034877016926835958109027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40023251344617890638739351 60034877016926835958109027)
            ·
              refine ⟨90052315525390253937163541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60034877016926835958109027 90052315525390253937163541)
              ·
                refine ⟨4221202290252668153304541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90052315525390253937163541 4221202290252668153304541)
                ·
                  refine ⟨1582950858844750557489203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4221202290252668153304541 1582950858844750557489203)
                  ·
                    refine ⟨2374426288267125836233805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582950858844750557489203 2374426288267125836233805)
                    ·
                      refine ⟨890409858100172188587677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374426288267125836233805 890409858100172188587677)
                      ·
                        rfl

theorem cell23_1734067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_1734067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734067 prefixEnd_1734067 := by exact prefixLift 1734067
  have htrace : WordTrace (prefixWord ++ tailWord_1734067) baseStart_1734067 baseEnd_1734067 := by
    simpa [prefixWord, tailWord_1734067, baseEnd_1734067] using wordTrace_append hprefix tailTrace_1734067
  have hstable : (prefixWord ++ tailWord_1734067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734067).length < 2 ^ (prefixWord ++ tailWord_1734067).sum := by decide
  have hdescent : baseEnd_1734067 < baseStart_1734067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734094 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_1734094 : Nat := 118140960795 + 1734094 * 2 ^ 59
def prefixEnd_1734094 : Nat := 4983230072969 + 3 ^ 40 * 1734094 * 2
def baseEnd_1734094 : Nat := 890423722077843582950053

theorem tailTrace_1734094 : CollatzResearch.WordTrace tailWord_1734094 prefixEnd_1734094 890423722077843582950053 := by
  unfold tailWord_1734094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905950522460134065229167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42165069453120715014555557 7905950522460134065229167)
  ·
    refine ⟨11858925783690201097843751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905950522460134065229167 11858925783690201097843751)
    ·
      refine ⟨17788388675535301646765627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858925783690201097843751 17788388675535301646765627)
      ·
        refine ⟨26682583013302952470148441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788388675535301646765627 26682583013302952470148441)
        ·
          refine ⟨20011937259977214352611331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26682583013302952470148441 20011937259977214352611331)
          ·
            refine ⟨30017905889965821528916997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20011937259977214352611331 30017905889965821528916997)
            ·
              refine ⟨5628357354368591536671937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30017905889965821528916997 5628357354368591536671937)
              ·
                refine ⟨4221268015776443652503953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628357354368591536671937 4221268015776443652503953)
                ·
                  refine ⟨3165951011832332739377965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221268015776443652503953 3165951011832332739377965)
                  ·
                    refine ⟨1187231629437124777266737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3165951011832332739377965 1187231629437124777266737)
                    ·
                      refine ⟨890423722077843582950053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187231629437124777266737 890423722077843582950053)
                      ·
                        rfl

theorem cell23_1734094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_1734094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734094 prefixEnd_1734094 := by exact prefixLift 1734094
  have htrace : WordTrace (prefixWord ++ tailWord_1734094) baseStart_1734094 baseEnd_1734094 := by
    simpa [prefixWord, tailWord_1734094, baseEnd_1734094] using wordTrace_append hprefix tailTrace_1734094
  have hstable : (prefixWord ++ tailWord_1734094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734094).length < 2 ^ (prefixWord ++ tailWord_1734094).sum := by decide
  have hdescent : baseEnd_1734094 < baseStart_1734094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734101 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1734101 : Nat := 118140960795 + 1734101 * 2 ^ 59
def prefixEnd_1734101 : Nat := 4983230072969 + 3 ^ 40 * 1734101 * 2
def baseEnd_1734101 : Nat := 890427316442425055562521

theorem tailTrace_1734101 : CollatzResearch.WordTrace tailWord_1734101 prefixEnd_1734101 890427316442425055562521 := by
  unfold tailWord_1734101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63247859490655712717338157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42165239660437141811558771 63247859490655712717338157)
  ·
    refine ⟨23717947308995892269001809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63247859490655712717338157 23717947308995892269001809)
    ·
      refine ⟨17788460481746919201751357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23717947308995892269001809 17788460481746919201751357)
      ·
        refine ⟨6670672680655094700656759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17788460481746919201751357 6670672680655094700656759)
        ·
          refine ⟨10006009020982642050985139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670672680655094700656759 10006009020982642050985139)
          ·
            refine ⟨15009013531473963076477709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006009020982642050985139 15009013531473963076477709)
            ·
              refine ⟨5628380074302736153679141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15009013531473963076477709 5628380074302736153679141)
              ·
                refine ⟨1055321263931763028814839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5628380074302736153679141 1055321263931763028814839)
                ·
                  refine ⟨1582981895897644543222259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055321263931763028814839 1582981895897644543222259)
                  ·
                    refine ⟨2374472843846466814833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582981895897644543222259 2374472843846466814833389)
                    ·
                      refine ⟨890427316442425055562521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374472843846466814833389 890427316442425055562521)
                      ·
                        rfl

theorem cell23_1734101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1734101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734101 prefixEnd_1734101 := by exact prefixLift 1734101
  have htrace : WordTrace (prefixWord ++ tailWord_1734101) baseStart_1734101 baseEnd_1734101 := by
    simpa [prefixWord, tailWord_1734101, baseEnd_1734101] using wordTrace_append hprefix tailTrace_1734101
  have hstable : (prefixWord ++ tailWord_1734101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734101).length < 2 ^ (prefixWord ++ tailWord_1734101).sum := by decide
  have hdescent : baseEnd_1734101 < baseStart_1734101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734117 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_1734117 : Nat := 118140960795 + 1734117 * 2 ^ 59
def prefixEnd_1734117 : Nat := 4983230072969 + 3 ^ 40 * 1734117 * 2
def baseEnd_1734117 : Nat := 296811844044298997654149

theorem tailTrace_1734117 : CollatzResearch.WordTrace tailWord_1734117 prefixEnd_1734117 296811844044298997654149 := by
  unfold tailWord_1734117
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248443058597747449920605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42165628705731831633280403 63248443058597747449920605)
  ·
    refine ⟨23718166146974155293720227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63248443058597747449920605 23718166146974155293720227)
    ·
      refine ⟨35577249220461232940580341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23718166146974155293720227 35577249220461232940580341)
      ·
        refine ⟨3335367114418240588179407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35577249220461232940580341 3335367114418240588179407)
        ·
          refine ⟨5003050671627360882269111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335367114418240588179407 5003050671627360882269111)
          ·
            refine ⟨7504576007441041323403667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003050671627360882269111 7504576007441041323403667)
            ·
              refine ⟨11256864011161561985105501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504576007441041323403667 11256864011161561985105501)
              ·
                refine ⟨4221324004185585744414563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11256864011161561985105501 4221324004185585744414563)
                ·
                  refine ⟨6331986006278378616621845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221324004185585744414563 6331986006278378616621845)
                  ·
                    refine ⟨296811844044298997654149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6331986006278378616621845 296811844044298997654149)
                    ·
                      rfl

theorem cell23_1734117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_1734117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734117 prefixEnd_1734117 := by exact prefixLift 1734117
  have htrace : WordTrace (prefixWord ++ tailWord_1734117) baseStart_1734117 baseEnd_1734117 := by
    simpa [prefixWord, tailWord_1734117, baseEnd_1734117] using wordTrace_append hprefix tailTrace_1734117
  have hstable : (prefixWord ++ tailWord_1734117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734117).length < 2 ^ (prefixWord ++ tailWord_1734117).sum := by decide
  have hdescent : baseEnd_1734117 < baseStart_1734117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734127 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_1734127 : Nat := 118140960795 + 1734127 * 2 ^ 59
def prefixEnd_1734127 : Nat := 4983230072969 + 3 ^ 40 * 1734127 * 2
def baseEnd_1734127 : Nat := 890440666939441953837401

theorem tailTrace_1734127 : CollatzResearch.WordTrace tailWord_1734127 prefixEnd_1734127 890440666939441953837401 := by
  unfold tailWord_1734127
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248807788561519157784635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42165871859041012771856423 63248807788561519157784635)
  ·
    refine ⟨94873211682842278736676953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63248807788561519157784635 94873211682842278736676953)
    ·
      refine ⟨71154908762131709052507715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94873211682842278736676953 71154908762131709052507715)
      ·
        refine ⟨106732363143197563578761573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71154908762131709052507715 106732363143197563578761573)
        ·
          refine ⟨20012318089349543171017795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106732363143197563578761573 20012318089349543171017795)
          ·
            refine ⟨30018477134024314756526693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012318089349543171017795 30018477134024314756526693)
            ·
              refine ⟨5628464462629559016848755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30018477134024314756526693 5628464462629559016848755)
              ·
                refine ⟨8442696693944338525273133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628464462629559016848755 8442696693944338525273133)
                ·
                  refine ⟨3166011260229126946977425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8442696693944338525273133 3166011260229126946977425)
                  ·
                    refine ⟨2374508445171845210233069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3166011260229126946977425 2374508445171845210233069)
                    ·
                      refine ⟨890440666939441953837401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2374508445171845210233069 890440666939441953837401)
                      ·
                        rfl

theorem cell23_1734127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_1734127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734127 prefixEnd_1734127 := by exact prefixLift 1734127
  have htrace : WordTrace (prefixWord ++ tailWord_1734127) baseStart_1734127 baseEnd_1734127 := by
    simpa [prefixWord, tailWord_1734127, baseEnd_1734127] using wordTrace_append hprefix tailTrace_1734127
  have hstable : (prefixWord ++ tailWord_1734127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734127).length < 2 ^ (prefixWord ++ tailWord_1734127).sum := by decide
  have hdescent : baseEnd_1734127 < baseStart_1734127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734141 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_1734141 : Nat := 118140960795 + 1734141 * 2 ^ 59
def prefixEnd_1734141 : Nat := 4983230072969 + 3 ^ 40 * 1734141 * 2
def baseEnd_1734141 : Nat := 890447855668604899062337

theorem tailTrace_1734141 : CollatzResearch.WordTrace tailWord_1734141 prefixEnd_1734141 890447855668604899062337 := by
  unfold tailWord_1734141
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249318410510799548794277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42166212273673866365862851 63249318410510799548794277)
  ·
    refine ⟨11859247201970774915398927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63249318410510799548794277 11859247201970774915398927)
    ·
      refine ⟨17788870802956162373098391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859247201970774915398927 17788870802956162373098391)
      ·
        refine ⟨26683306204434243559647587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788870802956162373098391 26683306204434243559647587)
        ·
          refine ⟨40024959306651365339471381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26683306204434243559647587 40024959306651365339471381)
          ·
            refine ⟨1876169967499282750287721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40024959306651365339471381 1876169967499282750287721)
            ·
              refine ⟨1407127475624462062715791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876169967499282750287721 1407127475624462062715791)
              ·
                refine ⟨2110691213436693094073687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407127475624462062715791 2110691213436693094073687)
                ·
                  refine ⟨3166036820155039641110531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110691213436693094073687 3166036820155039641110531)
                  ·
                    refine ⟨4749055230232559461665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166036820155039641110531 4749055230232559461665797)
                    ·
                      refine ⟨890447855668604899062337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749055230232559461665797 890447855668604899062337)
                      ·
                        rfl

theorem cell23_1734141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_1734141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734141 prefixEnd_1734141 := by exact prefixLift 1734141
  have htrace : WordTrace (prefixWord ++ tailWord_1734141) baseStart_1734141 baseEnd_1734141 := by
    simpa [prefixWord, tailWord_1734141, baseEnd_1734141] using wordTrace_append hprefix tailTrace_1734141
  have hstable : (prefixWord ++ tailWord_1734141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734141).length < 2 ^ (prefixWord ++ tailWord_1734141).sum := by decide
  have hdescent : baseEnd_1734141 < baseStart_1734141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734151 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1734151 : Nat := 118140960795 + 1734151 * 2 ^ 59
def prefixEnd_1734151 : Nat := 4983230072969 + 3 ^ 40 * 1734151 * 2
def baseEnd_1734151 : Nat := 296817663491716619979097

theorem tailTrace_1734151 : CollatzResearch.WordTrace tailWord_1734151 prefixEnd_1734151 296817663491716619979097 := by
  unfold tailWord_1734151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249683140474571256658307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42166455426983047504438871 63249683140474571256658307)
  ·
    refine ⟨94874524710711856884987461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63249683140474571256658307 94874524710711856884987461)
    ·
      refine ⟨17788973383258473165935149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94874524710711856884987461 17788973383258473165935149)
      ·
        refine ⟨6670865018721927437225681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17788973383258473165935149 6670865018721927437225681)
        ·
          refine ⟨5003148764041445577919261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6670865018721927437225681 5003148764041445577919261)
          ·
            refine ⟨1876180786515542091719723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5003148764041445577919261 1876180786515542091719723)
            ·
              refine ⟨2814271179773313137579585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876180786515542091719723 2814271179773313137579585)
              ·
                refine ⟨2110703384829984853184689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814271179773313137579585 2110703384829984853184689)
                ·
                  refine ⟨1583027538622488639888517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2110703384829984853184689 1583027538622488639888517)
                  ·
                    refine ⟨296817663491716619979097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583027538622488639888517 296817663491716619979097)
                    ·
                      rfl

theorem cell23_1734151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1734151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734151 prefixEnd_1734151 := by exact prefixLift 1734151
  have htrace : WordTrace (prefixWord ++ tailWord_1734151) baseStart_1734151 baseEnd_1734151 := by
    simpa [prefixWord, tailWord_1734151, baseEnd_1734151] using wordTrace_append hprefix tailTrace_1734151
  have hstable : (prefixWord ++ tailWord_1734151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734151).length < 2 ^ (prefixWord ++ tailWord_1734151).sum := by decide
  have hdescent : baseEnd_1734151 < baseStart_1734151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734158 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1734158 : Nat := 118140960795 + 1734158 * 2 ^ 59
def prefixEnd_1734158 : Nat := 4983230072969 + 3 ^ 40 * 1734158 * 2
def baseEnd_1734158 : Nat := 890456584839731332549759

theorem tailTrace_1734158 : CollatzResearch.WordTrace tailWord_1734158 prefixEnd_1734158 890456584839731332549759 := by
  unfold tailWord_1734158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906242306431151431520391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42166625634299474301442085 7906242306431151431520391)
  ·
    refine ⟨11859363459646727147280587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7906242306431151431520391 11859363459646727147280587)
    ·
      refine ⟨17789045189470090720920881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859363459646727147280587 17789045189470090720920881)
      ·
        refine ⟨13341783892102568040690661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17789045189470090720920881 13341783892102568040690661)
        ·
          refine ⟨2501584479769231507629499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13341783892102568040690661 2501584479769231507629499)
          ·
            refine ⟨3752376719653847261444249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501584479769231507629499 3752376719653847261444249)
            ·
              refine ⟨2814282539740385446083187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752376719653847261444249 2814282539740385446083187)
              ·
                refine ⟨4221423809610578169124781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814282539740385446083187 4221423809610578169124781)
                ·
                  refine ⟨1583033928603966813421793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4221423809610578169124781 1583033928603966813421793)
                  ·
                    refine ⟨1187275446452975110066345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1583033928603966813421793 1187275446452975110066345)
                    ·
                      refine ⟨890456584839731332549759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187275446452975110066345 890456584839731332549759)
                      ·
                        rfl

theorem cell23_1734158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1734158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734158 prefixEnd_1734158 := by exact prefixLift 1734158
  have htrace : WordTrace (prefixWord ++ tailWord_1734158) baseStart_1734158 baseEnd_1734158 := by
    simpa [prefixWord, tailWord_1734158, baseEnd_1734158] using wordTrace_append hprefix tailTrace_1734158
  have hstable : (prefixWord ++ tailWord_1734158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734158).length < 2 ^ (prefixWord ++ tailWord_1734158).sum := by decide
  have hdescent : baseEnd_1734158 < baseStart_1734158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734201 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1734201 : Nat := 118140960795 + 1734201 * 2 ^ 59
def prefixEnd_1734201 : Nat := 4983230072969 + 3 ^ 40 * 1734201 * 2
def baseEnd_1734201 : Nat := 890478664507874664312061

theorem tailTrace_1734201 : CollatzResearch.WordTrace tailWord_1734201 prefixEnd_1734201 890478664507874664312061 := by
  unfold tailWord_1734201
  simp only [CollatzResearch.WordTrace]
  refine ⟨63251506790293429795978457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42167671193528953197318971 63251506790293429795978457)
  ·
    refine ⟨47438630092720072346983843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63251506790293429795978457 47438630092720072346983843)
    ·
      refine ⟨71157945139080108520475765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47438630092720072346983843 71157945139080108520475765)
      ·
        refine ⟨6671057356788760173794603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71157945139080108520475765 6671057356788760173794603)
        ·
          refine ⟨10006586035183140260691905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671057356788760173794603 10006586035183140260691905)
          ·
            refine ⟨7504939526387355195518929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006586035183140260691905 7504939526387355195518929)
            ·
              refine ⟨5628704644790516396639197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504939526387355195518929 5628704644790516396639197)
              ·
                refine ⟨2110764241796443648739699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5628704644790516396639197 2110764241796443648739699)
                ·
                  refine ⟨3166146362694665473109549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110764241796443648739699 3166146362694665473109549)
                  ·
                    refine ⟨1187304886010499552416081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166146362694665473109549 1187304886010499552416081)
                    ·
                      refine ⟨890478664507874664312061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187304886010499552416081 890478664507874664312061)
                      ·
                        rfl

theorem cell23_1734201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1734201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734201 prefixEnd_1734201 := by exact prefixLift 1734201
  have htrace : WordTrace (prefixWord ++ tailWord_1734201) baseStart_1734201 baseEnd_1734201 := by
    simpa [prefixWord, tailWord_1734201, baseEnd_1734201] using wordTrace_append hprefix tailTrace_1734201
  have hstable : (prefixWord ++ tailWord_1734201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734201).length < 2 ^ (prefixWord ++ tailWord_1734201).sum := by decide
  have hdescent : baseEnd_1734201 < baseStart_1734201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734267 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 2, 5]
def baseStart_1734267 : Nat := 118140960795 + 1734267 * 2 ^ 59
def prefixEnd_1734267 : Nat := 4983230072969 + 3 ^ 40 * 1734267 * 2
def baseEnd_1734267 : Nat := 296837518077023802028919

theorem tailTrace_1734267 : CollatzResearch.WordTrace tailWord_1734267 prefixEnd_1734267 296837518077023802028919 := by
  unfold tailWord_1734267
  simp only [CollatzResearch.WordTrace]
  refine ⟨63253914008054323067881055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42169276005369548711920703 63253914008054323067881055)
  ·
    refine ⟨94880871012081484601821583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63253914008054323067881055 94880871012081484601821583)
    ·
      refine ⟨142321306518122226902732375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94880871012081484601821583 142321306518122226902732375)
      ·
        refine ⟨213481959777183340354098563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142321306518122226902732375 213481959777183340354098563)
        ·
          refine ⟨320222939665775010531147845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213481959777183340354098563 320222939665775010531147845)
          ·
            refine ⟨60041801187332814474590221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320222939665775010531147845 60041801187332814474590221)
            ·
              refine ⟨22515675445249805427971333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60041801187332814474590221 22515675445249805427971333)
              ·
                refine ⟨4221689145984338517744625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22515675445249805427971333 4221689145984338517744625)
                ·
                  refine ⟨3166266859488253888308469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221689145984338517744625 3166266859488253888308469)
                  ·
                    refine ⟨296837518077023802028919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3166266859488253888308469 296837518077023802028919)
                    ·
                      rfl

theorem cell23_1734267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].length) (baseStart_1734267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734267 prefixEnd_1734267 := by exact prefixLift 1734267
  have htrace : WordTrace (prefixWord ++ tailWord_1734267) baseStart_1734267 baseEnd_1734267 := by
    simpa [prefixWord, tailWord_1734267, baseEnd_1734267] using wordTrace_append hprefix tailTrace_1734267
  have hstable : (prefixWord ++ tailWord_1734267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734267).length < 2 ^ (prefixWord ++ tailWord_1734267).sum := by decide
  have hdescent : baseEnd_1734267 < baseStart_1734267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734277 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1734277 : Nat := 118140960795 + 1734277 * 2 ^ 59
def prefixEnd_1734277 : Nat := 4983230072969 + 3 ^ 40 * 1734277 * 2
def baseEnd_1734277 : Nat := 890517689037616366961711

theorem tailTrace_1734277 : CollatzResearch.WordTrace tailWord_1734277 prefixEnd_1734277 890517689037616366961711 := by
  unfold tailWord_1734277
  simp only [CollatzResearch.WordTrace]
  refine ⟨63254278738018094775745085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42169519158678729850496723 63254278738018094775745085)
  ·
    refine ⟨23720354526756785540904407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63254278738018094775745085 23720354526756785540904407)
    ·
      refine ⟨35580531790135178311356611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23720354526756785540904407 35580531790135178311356611)
      ·
        refine ⟨53370797685202767467034917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35580531790135178311356611 53370797685202767467034917)
        ·
          refine ⟨10007024565975518900069047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53370797685202767467034917 10007024565975518900069047)
          ·
            refine ⟨15010536848963278350103571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10007024565975518900069047 15010536848963278350103571)
            ·
              refine ⟨22515805273444917525155357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15010536848963278350103571 22515805273444917525155357)
              ·
                refine ⟨8443426977541844071933259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22515805273444917525155357 8443426977541844071933259)
                ·
                  refine ⟨12665140466312766107899889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8443426977541844071933259 12665140466312766107899889)
                  ·
                    refine ⟨9498855349734574580924917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12665140466312766107899889 9498855349734574580924917)
                    ·
                      refine ⟨890517689037616366961711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9498855349734574580924917 890517689037616366961711)
                      ·
                        rfl

theorem cell23_1734277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1734277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734277 prefixEnd_1734277 := by exact prefixLift 1734277
  have htrace : WordTrace (prefixWord ++ tailWord_1734277) baseStart_1734277 baseEnd_1734277 := by
    simpa [prefixWord, tailWord_1734277, baseEnd_1734277] using wordTrace_append hprefix tailTrace_1734277
  have hstable : (prefixWord ++ tailWord_1734277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734277).length < 2 ^ (prefixWord ++ tailWord_1734277).sum := by decide
  have hdescent : baseEnd_1734277 < baseStart_1734277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734304 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1734304 : Nat := 118140960795 + 1734304 * 2 ^ 59
def prefixEnd_1734304 : Nat := 4983230072969 + 3 ^ 40 * 1734304 * 2
def baseEnd_1734304 : Nat := 890531553015287761324087

theorem tailTrace_1734304 : CollatzResearch.WordTrace tailWord_1734304 prefixEnd_1734304 890531553015287761324087 := by
  unfold tailWord_1734304
  simp only [CollatzResearch.WordTrace]
  refine ⟨31627631754460139193488983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42170175672613518924651977 31627631754460139193488983)
  ·
    refine ⟨47441447631690208790233475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31627631754460139193488983 47441447631690208790233475)
    ·
      refine ⟨71162171447535313185350213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47441447631690208790233475 71162171447535313185350213)
      ·
        refine ⟨13342907146412871222253165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71162171447535313185350213 13342907146412871222253165)
        ·
          refine ⟨5003590179904826708344937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13342907146412871222253165 5003590179904826708344937)
          ·
            refine ⟨3752692634928620031258703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003590179904826708344937 3752692634928620031258703)
            ·
              refine ⟨5629038952392930046888055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752692634928620031258703 5629038952392930046888055)
              ·
                refine ⟨8443558428589395070332083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629038952392930046888055 8443558428589395070332083)
                ·
                  refine ⟨12665337642884092605498125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8443558428589395070332083 12665337642884092605498125)
                  ·
                    refine ⟨4749501616081534727061797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12665337642884092605498125 4749501616081534727061797)
                    ·
                      refine ⟨890531553015287761324087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749501616081534727061797 890531553015287761324087)
                      ·
                        rfl

theorem cell23_1734304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1734304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734304 prefixEnd_1734304 := by exact prefixLift 1734304
  have htrace : WordTrace (prefixWord ++ tailWord_1734304) baseStart_1734304 baseEnd_1734304 := by
    simpa [prefixWord, tailWord_1734304, baseEnd_1734304] using wordTrace_append hprefix tailTrace_1734304
  have hstable : (prefixWord ++ tailWord_1734304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734304).length < 2 ^ (prefixWord ++ tailWord_1734304).sum := by decide
  have hdescent : baseEnd_1734304 < baseStart_1734304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734394 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1734394 : Nat := 118140960795 + 1734394 * 2 ^ 59
def prefixEnd_1734394 : Nat := 4983230072969 + 3 ^ 40 * 1734394 * 2
def baseEnd_1734394 : Nat := 890577766274192409198673

theorem tailTrace_1734394 : CollatzResearch.WordTrace tailWord_1734394 prefixEnd_1734394 890577766274192409198673 := by
  unfold tailWord_1734394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814636519648555939438559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42172364052396149171836157 15814636519648555939438559)
  ·
    refine ⟨23721954779472833909157839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814636519648555939438559 23721954779472833909157839)
    ·
      refine ⟨35582932169209250863736759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721954779472833909157839 35582932169209250863736759)
      ·
        refine ⟨53374398253813876295605139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35582932169209250863736759 53374398253813876295605139)
        ·
          refine ⟨80061597380720814443407709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53374398253813876295605139 80061597380720814443407709)
          ·
            refine ⟨30023099017770305416277891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80061597380720814443407709 30023099017770305416277891)
            ·
              refine ⟨45034648526655458124416837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30023099017770305416277891 45034648526655458124416837)
              ·
                refine ⟨8443996598747898398328157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45034648526655458124416837 8443996598747898398328157)
                ·
                  refine ⟨3166498724530461899373059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8443996598747898398328157 3166498724530461899373059)
                  ·
                    refine ⟨4749748086795692849059589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166498724530461899373059 4749748086795692849059589)
                    ·
                      refine ⟨890577766274192409198673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749748086795692849059589 890577766274192409198673)
                      ·
                        rfl

theorem cell23_1734394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1734394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734394 prefixEnd_1734394 := by exact prefixLift 1734394
  have htrace : WordTrace (prefixWord ++ tailWord_1734394) baseStart_1734394 baseEnd_1734394 := by
    simpa [prefixWord, tailWord_1734394, baseEnd_1734394] using wordTrace_append hprefix tailTrace_1734394
  have hstable : (prefixWord ++ tailWord_1734394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734394).length < 2 ^ (prefixWord ++ tailWord_1734394).sum := by decide
  have hdescent : baseEnd_1734394 < baseStart_1734394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734411 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 4]
def baseStart_1734411 : Nat := 118140960795 + 1734411 * 2 ^ 59
def prefixEnd_1734411 : Nat := 4983230072969 + 3 ^ 40 * 1734411 * 2
def baseEnd_1734411 : Nat := 890586495445318842686095

theorem tailTrace_1734411 : CollatzResearch.WordTrace tailWord_1734411 prefixEnd_1734411 890586495445318842686095 := by
  unfold tailWord_1734411
  simp only [CollatzResearch.WordTrace]
  refine ⟨63259166119532635661123087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42172777413021757107415391 63259166119532635661123087)
  ·
    refine ⟨94888749179298953491684631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63259166119532635661123087 94888749179298953491684631)
    ·
      refine ⟨142333123768948430237526947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94888749179298953491684631 142333123768948430237526947)
      ·
        refine ⟨213499685653422645356290421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142333123768948430237526947 213499685653422645356290421)
        ·
          refine ⟨20015595530008373002152227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213499685653422645356290421 20015595530008373002152227)
          ·
            refine ⟨30023393295012559503228341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015595530008373002152227 30023393295012559503228341)
            ·
              refine ⟨2814693121407427453427657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30023393295012559503228341 2814693121407427453427657)
              ·
                refine ⟨2111019841055570590070743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814693121407427453427657 2111019841055570590070743)
                ·
                  refine ⟨3166529761583355885106115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111019841055570590070743 3166529761583355885106115)
                  ·
                    refine ⟨4749794642375033827659173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166529761583355885106115 4749794642375033827659173)
                    ·
                      refine ⟨890586495445318842686095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749794642375033827659173 890586495445318842686095)
                      ·
                        rfl

theorem cell23_1734411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 4].length) (baseStart_1734411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734411 prefixEnd_1734411 := by exact prefixLift 1734411
  have htrace : WordTrace (prefixWord ++ tailWord_1734411) baseStart_1734411 baseEnd_1734411 := by
    simpa [prefixWord, tailWord_1734411, baseEnd_1734411] using wordTrace_append hprefix tailTrace_1734411
  have hstable : (prefixWord ++ tailWord_1734411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734411).length < 2 ^ (prefixWord ++ tailWord_1734411).sum := by decide
  have hdescent : baseEnd_1734411 < baseStart_1734411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734414 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1734414 : Nat := 118140960795 + 1734414 * 2 ^ 59
def prefixEnd_1734414 : Nat := 4983230072969 + 3 ^ 40 * 1734414 * 2
def baseEnd_1734414 : Nat := 890588035887282330948581

theorem tailTrace_1734414 : CollatzResearch.WordTrace tailWord_1734414 prefixEnd_1734414 890588035887282330948581 := by
  unfold tailWord_1734414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907409442315220896685287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42172850359014511448988197 7907409442315220896685287)
  ·
    refine ⟨11861114163472831345027931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907409442315220896685287 11861114163472831345027931)
    ·
      refine ⟨17791671245209247017541897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861114163472831345027931 17791671245209247017541897)
      ·
        refine ⟨13343753433906935263156423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17791671245209247017541897 13343753433906935263156423)
        ·
          refine ⟨20015630150860402894734635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343753433906935263156423 20015630150860402894734635)
          ·
            refine ⟨30023445226290604342101953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015630150860402894734635 30023445226290604342101953)
            ·
              refine ⟨22517583919717953256576465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30023445226290604342101953 22517583919717953256576465)
              ·
                refine ⟨16888187939788464942432349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22517583919717953256576465 16888187939788464942432349)
                ·
                  refine ⟨6333070477420674353412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16888187939788464942432349 6333070477420674353412131)
                  ·
                    refine ⟨9499605716131011530118197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333070477420674353412131 9499605716131011530118197)
                    ·
                      refine ⟨890588035887282330948581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9499605716131011530118197 890588035887282330948581)
                      ·
                        rfl

theorem cell23_1734414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1734414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734414 prefixEnd_1734414 := by exact prefixLift 1734414
  have htrace : WordTrace (prefixWord ++ tailWord_1734414) baseStart_1734414 baseEnd_1734414 := by
    simpa [prefixWord, tailWord_1734414, baseEnd_1734414] using wordTrace_append hprefix tailTrace_1734414
  have hstable : (prefixWord ++ tailWord_1734414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734414).length < 2 ^ (prefixWord ++ tailWord_1734414).sum := by decide
  have hdescent : baseEnd_1734414 < baseStart_1734414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734424 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1734424 : Nat := 118140960795 + 1734424 * 2 ^ 59
def prefixEnd_1734424 : Nat := 4983230072969 + 3 ^ 40 * 1734424 * 2
def baseEnd_1734424 : Nat := 890593170693827291823535

theorem tailTrace_1734424 : CollatzResearch.WordTrace tailWord_1734424 prefixEnd_1734424 890593170693827291823535 := by
  unfold tailWord_1734424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629820134242769440673163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42173093512323692587564217 31629820134242769440673163)
  ·
    refine ⟨47444730201364154161009745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31629820134242769440673163 47444730201364154161009745)
    ·
      refine ⟨35583547651023115620757309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47444730201364154161009745 35583547651023115620757309)
      ·
        refine ⟨13343830369133668357783991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35583547651023115620757309 13343830369133668357783991)
        ·
          refine ⟨20015745553700502536675987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343830369133668357783991 20015745553700502536675987)
          ·
            refine ⟨30023618330550753805013981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015745553700502536675987 30023618330550753805013981)
            ·
              refine ⟨11258856873956532676880243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30023618330550753805013981 11258856873956532676880243)
              ·
                refine ⟨16888285310934799015320365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11258856873956532676880243 16888285310934799015320365)
                ·
                  refine ⟨6333106991600549630745137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16888285310934799015320365 6333106991600549630745137)
                  ·
                    refine ⟨4749830243700412223058853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333106991600549630745137 4749830243700412223058853)
                    ·
                      refine ⟨890593170693827291823535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749830243700412223058853 890593170693827291823535)
                      ·
                        rfl

theorem cell23_1734424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1734424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734424 prefixEnd_1734424 := by exact prefixLift 1734424
  have htrace : WordTrace (prefixWord ++ tailWord_1734424) baseStart_1734424 baseEnd_1734424 := by
    simpa [prefixWord, tailWord_1734424, baseEnd_1734424] using wordTrace_append hprefix tailTrace_1734424
  have hstable : (prefixWord ++ tailWord_1734424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734424).length < 2 ^ (prefixWord ++ tailWord_1734424).sum := by decide
  have hdescent : baseEnd_1734424 < baseStart_1734424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734428 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1734428 : Nat := 118140960795 + 1734428 * 2 ^ 59
def prefixEnd_1734428 : Nat := 4983230072969 + 3 ^ 40 * 1734428 * 2
def baseEnd_1734428 : Nat := 890595224616445276173517

theorem tailTrace_1734428 : CollatzResearch.WordTrace tailWord_1734428 prefixEnd_1734428 890595224616445276173517 := by
  unfold tailWord_1734428
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629893080235523782245969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42173190773647365042994625 31629893080235523782245969)
  ·
    refine ⟨23722419810176642836684477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31629893080235523782245969 23722419810176642836684477)
    ·
      refine ⟨8895907428816241063756679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23722419810176642836684477 8895907428816241063756679)
      ·
        refine ⟨13343861143224361595635019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895907428816241063756679 13343861143224361595635019)
        ·
          refine ⟨20015791714836542393452529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343861143224361595635019 20015791714836542393452529)
          ·
            refine ⟨15011843786127406795089397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20015791714836542393452529 15011843786127406795089397)
            ·
              refine ⟨1407360354949444387039631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15011843786127406795089397 1407360354949444387039631)
              ·
                refine ⟨2111040532424166580559447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407360354949444387039631 2111040532424166580559447)
                ·
                  refine ⟨3166560798636249870839171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111040532424166580559447 3166560798636249870839171)
                  ·
                    refine ⟨4749841197954374806258757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166560798636249870839171 4749841197954374806258757)
                    ·
                      refine ⟨890595224616445276173517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4749841197954374806258757 890595224616445276173517)
                      ·
                        rfl

theorem cell23_1734428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1734428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734428 prefixEnd_1734428 := by exact prefixLift 1734428
  have htrace : WordTrace (prefixWord ++ tailWord_1734428) baseStart_1734428 baseEnd_1734428 := by
    simpa [prefixWord, tailWord_1734428, baseEnd_1734428] using wordTrace_append hprefix tailTrace_1734428
  have hstable : (prefixWord ++ tailWord_1734428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734428).length < 2 ^ (prefixWord ++ tailWord_1734428).sum := by decide
  have hdescent : baseEnd_1734428 < baseStart_1734428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734451 : List Nat := [1, 1, 1, 2, 7, 2, 1, 8]
def baseStart_1734451 : Nat := 118140960795 + 1734451 * 2 ^ 59
def prefixEnd_1734451 : Nat := 4983230072969 + 3 ^ 40 * 1734451 * 2
def baseEnd_1734451 : Nat := 32985445728574025414293

theorem tailTrace_1734451 : CollatzResearch.WordTrace tailWord_1734451 prefixEnd_1734451 32985445728574025414293 := by
  unfold tailWord_1734451
  simp only [CollatzResearch.WordTrace]
  refine ⟨63260625039387722492579207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42173750026258481661719471 63260625039387722492579207)
  ·
    refine ⟨94890937559081583738868811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63260625039387722492579207 94890937559081583738868811)
    ·
      refine ⟨142336406338622375608303217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94890937559081583738868811 142336406338622375608303217)
      ·
        refine ⟨106752304753966781706227413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142336406338622375608303217 106752304753966781706227413)
        ·
          refine ⟨2502007142671096446239705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 106752304753966781706227413 2502007142671096446239705)
          ·
            refine ⟨1876505357003322334679779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502007142671096446239705 1876505357003322334679779)
            ·
              refine ⟨2814758035504983502019669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876505357003322334679779 2814758035504983502019669)
              ·
                refine ⟨32985445728574025414293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2814758035504983502019669 32985445728574025414293)
                ·
                  rfl

theorem cell23_1734451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 8].length) (baseStart_1734451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734451 prefixEnd_1734451 := by exact prefixLift 1734451
  have htrace : WordTrace (prefixWord ++ tailWord_1734451) baseStart_1734451 baseEnd_1734451 := by
    simpa [prefixWord, tailWord_1734451, baseEnd_1734451] using wordTrace_append hprefix tailTrace_1734451
  have hstable : (prefixWord ++ tailWord_1734451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734451).length < 2 ^ (prefixWord ++ tailWord_1734451).sum := by decide
  have hdescent : baseEnd_1734451 < baseStart_1734451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734474 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1734474 : Nat := 118140960795 + 1734474 * 2 ^ 59
def prefixEnd_1734474 : Nat := 4983230072969 + 3 ^ 40 * 1734474 * 2
def baseEnd_1734474 : Nat := 890618844726552096198305

theorem tailTrace_1734474 : CollatzResearch.WordTrace tailWord_1734474 prefixEnd_1734474 890618844726552096198305 := by
  unfold tailWord_1734474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815365979576099355166619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42174309278869598280444317 15815365979576099355166619)
  ·
    refine ⟨23723048969364149032749929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815365979576099355166619 23723048969364149032749929)
    ·
      refine ⟨17792286727023111774562447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23723048969364149032749929 17792286727023111774562447)
      ·
        refine ⟨26688430090534667661843671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792286727023111774562447 26688430090534667661843671)
        ·
          refine ⟨40032645135802001492765507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26688430090534667661843671 40032645135802001492765507)
          ·
            refine ⟨60048967703703002239148261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40032645135802001492765507 60048967703703002239148261)
            ·
              refine ⟨11259181444444312919840299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60048967703703002239148261 11259181444444312919840299)
              ·
                refine ⟨16888772166666469379760449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11259181444444312919840299 16888772166666469379760449)
                ·
                  refine ⟨12666579124999852034820337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16888772166666469379760449 12666579124999852034820337)
                  ·
                    refine ⟨9499934343749889026115253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12666579124999852034820337 9499934343749889026115253)
                    ·
                      refine ⟨890618844726552096198305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9499934343749889026115253 890618844726552096198305)
                      ·
                        rfl

theorem cell23_1734474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1734474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734474 prefixEnd_1734474 := by exact prefixLift 1734474
  have htrace : WordTrace (prefixWord ++ tailWord_1734474) baseStart_1734474 baseEnd_1734474 := by
    simpa [prefixWord, tailWord_1734474, baseEnd_1734474] using wordTrace_append hprefix tailTrace_1734474
  have hstable : (prefixWord ++ tailWord_1734474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734474).length < 2 ^ (prefixWord ++ tailWord_1734474).sum := by decide
  have hdescent : baseEnd_1734474 < baseStart_1734474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734495 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1734495 : Nat := 118140960795 + 1734495 * 2 ^ 59
def prefixEnd_1734495 : Nat := 4983230072969 + 3 ^ 40 * 1734495 * 2
def baseEnd_1734495 : Nat := 890629627820296514035709

theorem tailTrace_1734495 : CollatzResearch.WordTrace tailWord_1734495 prefixEnd_1734495 890629627820296514035709 := by
  unfold tailWord_1734495
  simp only [CollatzResearch.WordTrace]
  refine ⟨63262229851228318007180939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42174819900818878671453959 63262229851228318007180939)
  ·
    refine ⟨94893344776842477010771409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63262229851228318007180939 94893344776842477010771409)
    ·
      refine ⟨71170008582631857758078557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94893344776842477010771409 71170008582631857758078557)
      ·
        refine ⟨26688753218486946659279459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71170008582631857758078557 26688753218486946659279459)
        ·
          refine ⟨40033129827730419988919189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26688753218486946659279459 40033129827730419988919189)
          ·
            refine ⟨1876552960674863436980587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40033129827730419988919189 1876552960674863436980587)
            ·
              refine ⟨2814829441012295155470881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876552960674863436980587 2814829441012295155470881)
              ·
                refine ⟨2111122080759221366603161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814829441012295155470881 2111122080759221366603161)
                ·
                  refine ⟨1583341560569416024952371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111122080759221366603161 1583341560569416024952371)
                  ·
                    refine ⟨2375012340854124037428557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1583341560569416024952371 2375012340854124037428557)
                    ·
                      refine ⟨890629627820296514035709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2375012340854124037428557 890629627820296514035709)
                      ·
                        rfl

theorem cell23_1734495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1734495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734495 prefixEnd_1734495 := by exact prefixLift 1734495
  have htrace : WordTrace (prefixWord ++ tailWord_1734495) baseStart_1734495 baseEnd_1734495 := by
    simpa [prefixWord, tailWord_1734495, baseEnd_1734495] using wordTrace_append hprefix tailTrace_1734495
  have hstable : (prefixWord ++ tailWord_1734495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734495).length < 2 ^ (prefixWord ++ tailWord_1734495).sum := by decide
  have hdescent : baseEnd_1734495 < baseStart_1734495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734538 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1734538 : Nat := 118140960795 + 1734538 * 2 ^ 59
def prefixEnd_1734538 : Nat := 4983230072969 + 3 ^ 40 * 1734538 * 2
def baseEnd_1734538 : Nat := 890651707488439845798011

theorem tailTrace_1734538 : CollatzResearch.WordTrace tailWord_1734538 prefixEnd_1734538 890651707488439845798011 := by
  unfold tailWord_1734538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815949547518134087749067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42175865460048357567330845 15815949547518134087749067)
  ·
    refine ⟨23723924321277201131623601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815949547518134087749067 23723924321277201131623601)
    ·
      refine ⟨17792943240957900848717701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23723924321277201131623601 17792943240957900848717701)
      ·
        refine ⟨3336176857679606409134569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17792943240957900848717701 3336176857679606409134569)
        ·
          refine ⟨2502132643259704806850927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336176857679606409134569 2502132643259704806850927)
          ·
            refine ⟨3753198964889557210276391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502132643259704806850927 3753198964889557210276391)
            ·
              refine ⟨5629798447334335815414587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753198964889557210276391 5629798447334335815414587)
              ·
                refine ⟨8444697671001503723121881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629798447334335815414587 8444697671001503723121881)
                ·
                  refine ⟨6333523253251127792341411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444697671001503723121881 6333523253251127792341411)
                  ·
                    refine ⟨9500284879876691688512117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333523253251127792341411 9500284879876691688512117)
                    ·
                      refine ⟨890651707488439845798011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9500284879876691688512117 890651707488439845798011)
                      ·
                        rfl

theorem cell23_1734538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1734538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734538 prefixEnd_1734538 := by exact prefixLift 1734538
  have htrace : WordTrace (prefixWord ++ tailWord_1734538) baseStart_1734538 baseEnd_1734538 := by
    simpa [prefixWord, tailWord_1734538, baseEnd_1734538] using wordTrace_append hprefix tailTrace_1734538
  have hstable : (prefixWord ++ tailWord_1734538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734538).length < 2 ^ (prefixWord ++ tailWord_1734538).sum := by decide
  have hdescent : baseEnd_1734538 < baseStart_1734538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734601 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_1734601 : Nat := 118140960795 + 1734601 * 2 ^ 59
def prefixEnd_1734601 : Nat := 4983230072969 + 3 ^ 40 * 1734601 * 2
def baseEnd_1734601 : Nat := 296894685589891033103407

theorem tailTrace_1734601 : CollatzResearch.WordTrace tailWord_1734601 prefixEnd_1734601 296894685589891033103407 := by
  unfold tailWord_1734601
  simp only [CollatzResearch.WordTrace]
  refine ⟨63266095988844298110539657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42177397325896198740359771 63266095988844298110539657)
  ·
    refine ⟨47449571991633223582904743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63266095988844298110539657 47449571991633223582904743)
    ·
      refine ⟨71174357987449835374357115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47449571991633223582904743 71174357987449835374357115)
      ·
        refine ⟨106761536981174753061535673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71174357987449835374357115 106761536981174753061535673)
        ·
          refine ⟨80071152735881064796151755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106761536981174753061535673 80071152735881064796151755)
          ·
            refine ⟨120106729103821597194227633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80071152735881064796151755 120106729103821597194227633)
            ·
              refine ⟨90080046827866197895670725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120106729103821597194227633 90080046827866197895670725)
              ·
                refine ⟨16890008780224912105438261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90080046827866197895670725 16890008780224912105438261)
                ·
                  refine ⟨1583438323146085509884837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16890008780224912105438261 1583438323146085509884837)
                  ·
                    refine ⟨296894685589891033103407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583438323146085509884837 296894685589891033103407)
                    ·
                      rfl

theorem cell23_1734601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_1734601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734601 prefixEnd_1734601 := by exact prefixLift 1734601
  have htrace : WordTrace (prefixWord ++ tailWord_1734601) baseStart_1734601 baseEnd_1734601 := by
    simpa [prefixWord, tailWord_1734601, baseEnd_1734601] using wordTrace_append hprefix tailTrace_1734601
  have hstable : (prefixWord ++ tailWord_1734601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734601).length < 2 ^ (prefixWord ++ tailWord_1734601).sum := by decide
  have hdescent : baseEnd_1734601 < baseStart_1734601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734685 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_1734685 : Nat := 118140960795 + 1734685 * 2 ^ 59
def prefixEnd_1734685 : Nat := 4983230072969 + 3 ^ 40 * 1734685 * 2
def baseEnd_1734685 : Nat := 890727189144650770659835

theorem tailTrace_1734685 : CollatzResearch.WordTrace tailWord_1734685 prefixEnd_1734685 890727189144650770659835 := by
  unfold tailWord_1734685
  simp only [CollatzResearch.WordTrace]
  refine ⟨63269159720539980456597509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42179439813693320304398339 63269159720539980456597509)
  ·
    refine ⟨11862967447601246335612033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63269159720539980456597509 11862967447601246335612033)
    ·
      refine ⟨8897225585700934751709025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11862967447601246335612033 8897225585700934751709025)
      ·
        refine ⟨6672919189275701063781769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8897225585700934751709025 6672919189275701063781769)
        ·
          refine ⟨5004689391956775797836327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672919189275701063781769 5004689391956775797836327)
          ·
            refine ⟨7507034087935163696754491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004689391956775797836327 7507034087935163696754491)
            ·
              refine ⟨11260551131902745545131737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507034087935163696754491 11260551131902745545131737)
              ·
                refine ⟨8445413348927059158848803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11260551131902745545131737 8445413348927059158848803)
                ·
                  refine ⟨12668120023390588738273205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445413348927059158848803 12668120023390588738273205)
                  ·
                    refine ⟨1187636252192867694213113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12668120023390588738273205 1187636252192867694213113)
                    ·
                      refine ⟨890727189144650770659835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187636252192867694213113 890727189144650770659835)
                      ·
                        rfl

theorem cell23_1734685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_1734685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734685 prefixEnd_1734685 := by exact prefixLift 1734685
  have htrace : WordTrace (prefixWord ++ tailWord_1734685) baseStart_1734685 baseEnd_1734685 := by
    simpa [prefixWord, tailWord_1734685, baseEnd_1734685] using wordTrace_append hprefix tailTrace_1734685
  have hstable : (prefixWord ++ tailWord_1734685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734685).length < 2 ^ (prefixWord ++ tailWord_1734685).sum := by decide
  have hdescent : baseEnd_1734685 < baseStart_1734685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734732 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1734732 : Nat := 118140960795 + 1734732 * 2 ^ 59
def prefixEnd_1734732 : Nat := 4983230072969 + 3 ^ 40 * 1734732 * 2
def baseEnd_1734732 : Nat := 890751322735412086772119

theorem tailTrace_1734732 : CollatzResearch.WordTrace tailWord_1734732 prefixEnd_1734732 890751322735412086772119 := by
  unfold tailWord_1734732
  simp only [CollatzResearch.WordTrace]
  refine ⟨31635436975684853741779225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42180582634246471655705633 31635436975684853741779225)
  ·
    refine ⟨23726577731763640306334419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31635436975684853741779225 23726577731763640306334419)
    ·
      refine ⟨35589866597645460459501629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23726577731763640306334419 35589866597645460459501629)
      ·
        refine ⟨13346199974117047672313111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35589866597645460459501629 13346199974117047672313111)
        ·
          refine ⟨20019299961175571508469667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346199974117047672313111 20019299961175571508469667)
          ·
            refine ⟨30028949941763357262704501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20019299961175571508469667 30028949941763357262704501)
            ·
              refine ⟨2815214057040314743378547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30028949941763357262704501 2815214057040314743378547)
              ·
                refine ⟨4222821085560472115067821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815214057040314743378547 4222821085560472115067821)
                ·
                  refine ⟨1583557907085177043150433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4222821085560472115067821 1583557907085177043150433)
                  ·
                    refine ⟨1187668430313882782362825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1583557907085177043150433 1187668430313882782362825)
                    ·
                      refine ⟨890751322735412086772119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187668430313882782362825 890751322735412086772119)
                      ·
                        rfl

theorem cell23_1734732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1734732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734732 prefixEnd_1734732 := by exact prefixLift 1734732
  have htrace : WordTrace (prefixWord ++ tailWord_1734732) baseStart_1734732 baseEnd_1734732 := by
    simpa [prefixWord, tailWord_1734732, baseEnd_1734732] using wordTrace_append hprefix tailTrace_1734732
  have hstable : (prefixWord ++ tailWord_1734732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734732).length < 2 ^ (prefixWord ++ tailWord_1734732).sum := by decide
  have hdescent : baseEnd_1734732 < baseStart_1734732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734749 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1734749 : Nat := 118140960795 + 1734749 * 2 ^ 59
def prefixEnd_1734749 : Nat := 4983230072969 + 3 ^ 40 * 1734749 * 2
def baseEnd_1734749 : Nat := 890760051906538520259541

theorem tailTrace_1734749 : CollatzResearch.WordTrace tailWord_1734749 prefixEnd_1734749 890760051906538520259541 := by
  unfold tailWord_1734749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271493992308119386927301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42180995994872079591284867 63271493992308119386927301)
  ·
    refine ⟨11863405123557772385048869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63271493992308119386927301 11863405123557772385048869)
    ·
      refine ⟨2224388460667082322196663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11863405123557772385048869 2224388460667082322196663)
      ·
        refine ⟨3336582691000623483294995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224388460667082322196663 3336582691000623483294995)
        ·
          refine ⟨5004874036500935224942493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336582691000623483294995 5004874036500935224942493)
          ·
            refine ⟨1876827763687850709353435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5004874036500935224942493 1876827763687850709353435)
            ·
              refine ⟨2815241645531776064030153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876827763687850709353435 2815241645531776064030153)
              ·
                refine ⟨2111431234148832048022615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815241645531776064030153 2111431234148832048022615)
                ·
                  refine ⟨3167146851223248072033923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111431234148832048022615 3167146851223248072033923)
                  ·
                    refine ⟨4750720276834872108050885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167146851223248072033923 4750720276834872108050885)
                    ·
                      refine ⟨890760051906538520259541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4750720276834872108050885 890760051906538520259541)
                      ·
                        rfl

theorem cell23_1734749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1734749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734749 prefixEnd_1734749 := by exact prefixLift 1734749
  have htrace : WordTrace (prefixWord ++ tailWord_1734749) baseStart_1734749 baseEnd_1734749 := by
    simpa [prefixWord, tailWord_1734749, baseEnd_1734749] using wordTrace_append hprefix tailTrace_1734749
  have hstable : (prefixWord ++ tailWord_1734749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734749).length < 2 ^ (prefixWord ++ tailWord_1734749).sum := by decide
  have hdescent : baseEnd_1734749 < baseStart_1734749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734751 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 7]
def baseStart_1734751 : Nat := 118140960795 + 1734751 * 2 ^ 59
def prefixEnd_1734751 : Nat := 4983230072969 + 3 ^ 40 * 1734751 * 2
def baseEnd_1734751 : Nat := 296920359622615837478177

theorem tailTrace_1734751 : CollatzResearch.WordTrace tailWord_1734751 prefixEnd_1734751 296920359622615837478177 := by
  unfold tailWord_1734751
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271566938300873728500107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42181044625533915819000071 63271566938300873728500107)
  ·
    refine ⟨94907350407451310592750161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63271566938300873728500107 94907350407451310592750161)
    ·
      refine ⟨71180512805588482944562621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94907350407451310592750161 71180512805588482944562621)
      ·
        refine ⟨26692692302095681104210983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71180512805588482944562621 26692692302095681104210983)
        ·
          refine ⟨40039038453143521656316475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26692692302095681104210983 40039038453143521656316475)
          ·
            refine ⟨60058557679715282484474713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40039038453143521656316475 60058557679715282484474713)
            ·
              refine ⟨45043918259786461863356035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60058557679715282484474713 45043918259786461863356035)
              ·
                refine ⟨67565877389679692795034053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45043918259786461863356035 67565877389679692795034053)
                ·
                  refine ⟨12668602010564942399068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67565877389679692795034053 12668602010564942399068885)
                  ·
                    refine ⟨296920359622615837478177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12668602010564942399068885 296920359622615837478177)
                    ·
                      rfl

theorem cell23_1734751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_1734751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734751 prefixEnd_1734751 := by exact prefixLift 1734751
  have htrace : WordTrace (prefixWord ++ tailWord_1734751) baseStart_1734751 baseEnd_1734751 := by
    simpa [prefixWord, tailWord_1734751, baseEnd_1734751] using wordTrace_append hprefix tailTrace_1734751
  have hstable : (prefixWord ++ tailWord_1734751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734751).length < 2 ^ (prefixWord ++ tailWord_1734751).sum := by decide
  have hdescent : baseEnd_1734751 < baseStart_1734751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734752 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_1734752 : Nat := 118140960795 + 1734752 * 2 ^ 59
def prefixEnd_1734752 : Nat := 4983230072969 + 3 ^ 40 * 1734752 * 2
def baseEnd_1734752 : Nat := 890761592348502008522027

theorem tailTrace_1734752 : CollatzResearch.WordTrace tailWord_1734752 prefixEnd_1734752 890761592348502008522027 := by
  unfold tailWord_1734752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31635801705648625449643255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42181068940864833932857673 31635801705648625449643255)
  ·
    refine ⟨47453702558472938174464883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31635801705648625449643255 47453702558472938174464883)
    ·
      refine ⟨71180553837709407261697325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47453702558472938174464883 71180553837709407261697325)
      ·
        refine ⟨26692707689141027723136497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71180553837709407261697325 26692707689141027723136497)
        ·
          refine ⟨20019530766855770792352373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26692707689141027723136497 20019530766855770792352373)
          ·
            refine ⟨1876831009392728511783035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20019530766855770792352373 1876831009392728511783035)
            ·
              refine ⟨2815246514089092767674553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876831009392728511783035 2815246514089092767674553)
              ·
                refine ⟨2111434885566819575755915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815246514089092767674553 2111434885566819575755915)
                ·
                  refine ⟨3167152328350229363633873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111434885566819575755915 3167152328350229363633873)
                  ·
                    refine ⟨2375364246262672022725405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167152328350229363633873 2375364246262672022725405)
                    ·
                      refine ⟨890761592348502008522027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2375364246262672022725405 890761592348502008522027)
                      ·
                        rfl

theorem cell23_1734752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_1734752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734752 prefixEnd_1734752 := by exact prefixLift 1734752
  have htrace : WordTrace (prefixWord ++ tailWord_1734752) baseStart_1734752 baseEnd_1734752 := by
    simpa [prefixWord, tailWord_1734752, baseEnd_1734752] using wordTrace_append hprefix tailTrace_1734752
  have hstable : (prefixWord ++ tailWord_1734752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734752).length < 2 ^ (prefixWord ++ tailWord_1734752).sum := by decide
  have hdescent : baseEnd_1734752 < baseStart_1734752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734765 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1734765 : Nat := 118140960795 + 1734765 * 2 ^ 59
def prefixEnd_1734765 : Nat := 4983230072969 + 3 ^ 40 * 1734765 * 2
def baseEnd_1734765 : Nat := 890768267597010457659467

theorem tailTrace_1734765 : CollatzResearch.WordTrace tailWord_1734765 prefixEnd_1734765 890768267597010457659467 := by
  unfold tailWord_1734765
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272077560250154119509749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42181385040166769413006499 63272077560250154119509749)
  ·
    refine ⟨5931757271273451948704039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63272077560250154119509749 5931757271273451948704039)
    ·
      refine ⟨8897635906910177923056059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5931757271273451948704039 8897635906910177923056059)
      ·
        refine ⟨13346453860365266884584089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897635906910177923056059 13346453860365266884584089)
        ·
          refine ⟨10009840395273950163438067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13346453860365266884584089 10009840395273950163438067)
          ·
            refine ⟨15014760592910925245157101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10009840395273950163438067 15014760592910925245157101)
            ·
              refine ⟨5630535222341596966933913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15014760592910925245157101 5630535222341596966933913)
              ·
                refine ⟨4222901416756197725200435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5630535222341596966933913 4222901416756197725200435)
                ·
                  refine ⟨6334352125134296587800653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222901416756197725200435 6334352125134296587800653)
                  ·
                    refine ⟨2375382046925361220425245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6334352125134296587800653 2375382046925361220425245)
                    ·
                      refine ⟨890768267597010457659467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2375382046925361220425245 890768267597010457659467)
                      ·
                        rfl

theorem cell23_1734765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1734765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734765 prefixEnd_1734765 := by exact prefixLift 1734765
  have htrace : WordTrace (prefixWord ++ tailWord_1734765) baseStart_1734765 baseEnd_1734765 := by
    simpa [prefixWord, tailWord_1734765, baseEnd_1734765] using wordTrace_append hprefix tailTrace_1734765
  have hstable : (prefixWord ++ tailWord_1734765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734765).length < 2 ^ (prefixWord ++ tailWord_1734765).sum := by decide
  have hdescent : baseEnd_1734765 < baseStart_1734765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734788 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1734788 : Nat := 118140960795 + 1734788 * 2 ^ 59
def prefixEnd_1734788 : Nat := 4983230072969 + 3 ^ 40 * 1734788 * 2
def baseEnd_1734788 : Nat := 890780077652063867671861

theorem tailTrace_1734788 : CollatzResearch.WordTrace tailWord_1734788 prefixEnd_1734788 890780077652063867671861 := by
  unfold tailWord_1734788
  simp only [CollatzResearch.WordTrace]
  refine ⟨31636458219583414523798509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42181944292777886031731345 31636458219583414523798509)
  ·
    refine ⟨11863671832343780446424441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31636458219583414523798509 11863671832343780446424441)
    ·
      refine ⟨8897753874257835334818331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11863671832343780446424441 8897753874257835334818331)
      ·
        refine ⟨13346630811386753002227497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897753874257835334818331 13346630811386753002227497)
        ·
          refine ⟨10009973108540064751670623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13346630811386753002227497 10009973108540064751670623)
          ·
            refine ⟨15014959662810097127505935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10009973108540064751670623 15014959662810097127505935)
            ·
              refine ⟨22522439494215145691258903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014959662810097127505935 22522439494215145691258903)
              ·
                refine ⟨33783659241322718536888355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22522439494215145691258903 33783659241322718536888355)
                ·
                  refine ⟨50675488861984077805332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33783659241322718536888355 50675488861984077805332533)
                  ·
                    refine ⟨4750827080811007294249925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50675488861984077805332533 4750827080811007294249925)
                    ·
                      refine ⟨890780077652063867671861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4750827080811007294249925 890780077652063867671861)
                      ·
                        rfl

theorem cell23_1734788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1734788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734788 prefixEnd_1734788 := by exact prefixLift 1734788
  have htrace : WordTrace (prefixWord ++ tailWord_1734788) baseStart_1734788 baseEnd_1734788 := by
    simpa [prefixWord, tailWord_1734788, baseEnd_1734788] using wordTrace_append hprefix tailTrace_1734788
  have hstable : (prefixWord ++ tailWord_1734788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734788).length < 2 ^ (prefixWord ++ tailWord_1734788).sum := by decide
  have hdescent : baseEnd_1734788 < baseStart_1734788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734792 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1734792 : Nat := 118140960795 + 1734792 * 2 ^ 59
def prefixEnd_1734792 : Nat := 4983230072969 + 3 ^ 40 * 1734792 * 2
def baseEnd_1734792 : Nat := 890782131574681852021843

theorem tailTrace_1734792 : CollatzResearch.WordTrace tailWord_1734792 prefixEnd_1734792 890782131574681852021843 := by
  unfold tailWord_1734792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31636531165576168865371315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42182041554101558487161753 31636531165576168865371315)
  ·
    refine ⟨47454796748364253298056973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31636531165576168865371315 47454796748364253298056973)
    ·
      refine ⟨17795548780636594986771365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47454796748364253298056973 17795548780636594986771365)
      ·
        refine ⟨3336665396369361560019631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17795548780636594986771365 3336665396369361560019631)
        ·
          refine ⟨5004998094554042340029447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336665396369361560019631 5004998094554042340029447)
          ·
            refine ⟨7507497141831063510044171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004998094554042340029447 7507497141831063510044171)
            ·
              refine ⟨11261245712746595265066257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507497141831063510044171 11261245712746595265066257)
              ·
                refine ⟨8445934284559946448799693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11261245712746595265066257 8445934284559946448799693)
                ·
                  refine ⟨3167225356709979918299885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445934284559946448799693 3167225356709979918299885)
                  ·
                    refine ⟨1187709508766242469362457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167225356709979918299885 1187709508766242469362457)
                    ·
                      refine ⟨890782131574681852021843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187709508766242469362457 890782131574681852021843)
                      ·
                        rfl

theorem cell23_1734792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1734792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734792 prefixEnd_1734792 := by exact prefixLift 1734792
  have htrace : WordTrace (prefixWord ++ tailWord_1734792) baseStart_1734792 baseEnd_1734792 := by
    simpa [prefixWord, tailWord_1734792, baseEnd_1734792] using wordTrace_append hprefix tailTrace_1734792
  have hstable : (prefixWord ++ tailWord_1734792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734792).length < 2 ^ (prefixWord ++ tailWord_1734792).sum := by decide
  have hdescent : baseEnd_1734792 < baseStart_1734792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734826 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1734826 : Nat := 118140960795 + 1734826 * 2 ^ 59
def prefixEnd_1734826 : Nat := 4983230072969 + 3 ^ 40 * 1734826 * 2
def baseEnd_1734826 : Nat := 890799589916934718996687

theorem tailTrace_1734826 : CollatzResearch.WordTrace tailWord_1734826 prefixEnd_1734826 890799589916934718996687 := by
  unfold tailWord_1734826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818575603257290384370083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42182868275352774358320221 15818575603257290384370083)
  ·
    refine ⟨23727863404885935576555125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818575603257290384370083 23727863404885935576555125)
    ·
      refine ⟨2224487194208056460302043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23727863404885935576555125 2224487194208056460302043)
      ·
        refine ⟨3336730791312084690453065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224487194208056460302043 3336730791312084690453065)
        ·
          refine ⟨2502548093484063517839799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336730791312084690453065 2502548093484063517839799)
          ·
            refine ⟨3753822140226095276759699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502548093484063517839799 3753822140226095276759699)
            ·
              refine ⟨5630733210339142915139549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753822140226095276759699 5630733210339142915139549)
              ·
                refine ⟨2111524953877178593177331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5630733210339142915139549 2111524953877178593177331)
                ·
                  refine ⟨3167287430815767889765997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111524953877178593177331 3167287430815767889765997)
                  ·
                    refine ⟨1187732786555912958662249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167287430815767889765997 1187732786555912958662249)
                    ·
                      refine ⟨890799589916934718996687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187732786555912958662249 890799589916934718996687)
                      ·
                        rfl

theorem cell23_1734826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1734826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734826 prefixEnd_1734826 := by exact prefixLift 1734826
  have htrace : WordTrace (prefixWord ++ tailWord_1734826) baseStart_1734826 baseEnd_1734826 := by
    simpa [prefixWord, tailWord_1734826, baseEnd_1734826] using wordTrace_append hprefix tailTrace_1734826
  have hstable : (prefixWord ++ tailWord_1734826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734826).length < 2 ^ (prefixWord ++ tailWord_1734826).sum := by decide
  have hdescent : baseEnd_1734826 < baseStart_1734826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734839 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_1734839 : Nat := 118140960795 + 1734839 * 2 ^ 59
def prefixEnd_1734839 : Nat := 4983230072969 + 3 ^ 40 * 1734839 * 2
def baseEnd_1734839 : Nat := 890806265165443168134127

theorem tailTrace_1734839 : CollatzResearch.WordTrace tailWord_1734839 prefixEnd_1734839 890806265165443168134127 := by
  unfold tailWord_1734839
  simp only [CollatzResearch.WordTrace]
  refine ⟨63274776561982064757703571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42183184374654709838469047 63274776561982064757703571)
  ·
    refine ⟨94912164842973097136555357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63274776561982064757703571 94912164842973097136555357)
    ·
      refine ⟨35592061816114911426208259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94912164842973097136555357 35592061816114911426208259)
      ·
        refine ⟨53388092724172367139312389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35592061816114911426208259 53388092724172367139312389)
        ·
          refine ⟨10010267385782318838621073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53388092724172367139312389 10010267385782318838621073)
          ·
            refine ⟨7507700539336739128965805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10010267385782318838621073 7507700539336739128965805)
            ·
              refine ⟨2815387702251277173362177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7507700539336739128965805 2815387702251277173362177)
              ·
                refine ⟨2111540776688457880021633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815387702251277173362177 2111540776688457880021633)
                ·
                  refine ⟨1583655582516343410016225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111540776688457880021633 1583655582516343410016225)
                  ·
                    refine ⟨1187741686887257557512169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1583655582516343410016225 1187741686887257557512169)
                    ·
                      refine ⟨890806265165443168134127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187741686887257557512169 890806265165443168134127)
                      ·
                        rfl

theorem cell23_1734839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_1734839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734839 prefixEnd_1734839 := by exact prefixLift 1734839
  have htrace : WordTrace (prefixWord ++ tailWord_1734839) baseStart_1734839 baseEnd_1734839 := by
    simpa [prefixWord, tailWord_1734839, baseEnd_1734839] using wordTrace_append hprefix tailTrace_1734839
  have hstable : (prefixWord ++ tailWord_1734839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734839).length < 2 ^ (prefixWord ++ tailWord_1734839).sum := by decide
  have hdescent : baseEnd_1734839 < baseStart_1734839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734858 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1734858 : Nat := 118140960795 + 1734858 * 2 ^ 59
def prefixEnd_1734858 : Nat := 4983230072969 + 3 ^ 40 * 1734858 * 2
def baseEnd_1734858 : Nat := 296938673765959531265513

theorem tailTrace_1734858 : CollatzResearch.WordTrace tailWord_1734858 prefixEnd_1734858 296938673765959531265513 := by
  unfold tailWord_1734858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818867387228307750661307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42183646365942154001763485 15818867387228307750661307)
  ·
    refine ⟨23728301080842461625991961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818867387228307750661307 23728301080842461625991961)
    ·
      refine ⟨17796225810631846219493971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23728301080842461625991961 17796225810631846219493971)
      ·
        refine ⟨26694338715947769329240957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796225810631846219493971 26694338715947769329240957)
        ·
          refine ⟨10010377018480413498465359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26694338715947769329240957 10010377018480413498465359)
          ·
            refine ⟨15015565527720620247698039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010377018480413498465359 15015565527720620247698039)
            ·
              refine ⟨22523348291580930371547059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015565527720620247698039 22523348291580930371547059)
              ·
                refine ⟨33785022437371395557320589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523348291580930371547059 33785022437371395557320589)
                ·
                  refine ⟨12669383414014273333995221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33785022437371395557320589 12669383414014273333995221)
                  ·
                    refine ⟨296938673765959531265513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12669383414014273333995221 296938673765959531265513)
                    ·
                      rfl

theorem cell23_1734858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1734858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734858 prefixEnd_1734858 := by exact prefixLift 1734858
  have htrace : WordTrace (prefixWord ++ tailWord_1734858) baseStart_1734858 baseEnd_1734858 := by
    simpa [prefixWord, tailWord_1734858, baseEnd_1734858] using wordTrace_append hprefix tailTrace_1734858
  have hstable : (prefixWord ++ tailWord_1734858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734858).length < 2 ^ (prefixWord ++ tailWord_1734858).sum := by decide
  have hdescent : baseEnd_1734858 < baseStart_1734858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734865 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_1734865 : Nat := 118140960795 + 1734865 * 2 ^ 59
def prefixEnd_1734865 : Nat := 4983230072969 + 3 ^ 40 * 1734865 * 2
def baseEnd_1734865 : Nat := 890819615662460066409007

theorem tailTrace_1734865 : CollatzResearch.WordTrace tailWord_1734865 prefixEnd_1734865 890819615662460066409007 := by
  unfold tailWord_1734865
  simp only [CollatzResearch.WordTrace]
  refine ⟨63275724859887871198150049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42183816573258580798766699 63275724859887871198150049)
  ·
    refine ⟨47456793644915903398612537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63275724859887871198150049 47456793644915903398612537)
    ·
      refine ⟨35592595233686927548959403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47456793644915903398612537 35592595233686927548959403)
      ·
        refine ⟨53388892850530391323439105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35592595233686927548959403 53388892850530391323439105)
        ·
          refine ⟨40041669637897793492579329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53388892850530391323439105 40041669637897793492579329)
          ·
            refine ⟨30031252228423345119434497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40041669637897793492579329 30031252228423345119434497)
            ·
              refine ⟨22523439171317508839575873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031252228423345119434497 22523439171317508839575873)
              ·
                refine ⟨16892579378488131629681905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523439171317508839575873 16892579378488131629681905)
                ·
                  refine ⟨12669434533866098722261429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16892579378488131629681905 12669434533866098722261429)
                  ·
                    refine ⟨1187759487549946755212009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12669434533866098722261429 1187759487549946755212009)
                    ·
                      refine ⟨890819615662460066409007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187759487549946755212009 890819615662460066409007)
                      ·
                        rfl

theorem cell23_1734865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_1734865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734865 prefixEnd_1734865 := by exact prefixLift 1734865
  have htrace : WordTrace (prefixWord ++ tailWord_1734865) baseStart_1734865 baseEnd_1734865 := by
    simpa [prefixWord, tailWord_1734865, baseEnd_1734865] using wordTrace_append hprefix tailTrace_1734865
  have hstable : (prefixWord ++ tailWord_1734865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734865).length < 2 ^ (prefixWord ++ tailWord_1734865).sum := by decide
  have hdescent : baseEnd_1734865 < baseStart_1734865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734895 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_1734895 : Nat := 118140960795 + 1734895 * 2 ^ 59
def prefixEnd_1734895 : Nat := 4983230072969 + 3 ^ 40 * 1734895 * 2
def baseEnd_1734895 : Nat := 890835020082094949033869

theorem tailTrace_1734895 : CollatzResearch.WordTrace tailWord_1734895 prefixEnd_1734895 890835020082094949033869 := by
  unfold tailWord_1734895
  simp only [CollatzResearch.WordTrace]
  refine ⟨63276819049779186321742139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42184546033186124214494759 63276819049779186321742139)
  ·
    refine ⟨94915228574668779482613209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63276819049779186321742139 94915228574668779482613209)
    ·
      refine ⟨71186421431001584611959907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94915228574668779482613209 71186421431001584611959907)
      ·
        refine ⟨106779632146502376917939861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71186421431001584611959907 106779632146502376917939861)
        ·
          refine ⟨5005295256867298918028431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106779632146502376917939861 5005295256867298918028431)
          ·
            refine ⟨7507942885300948377042647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005295256867298918028431 7507942885300948377042647)
            ·
              refine ⟨11261914327951422565563971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507942885300948377042647 11261914327951422565563971)
              ·
                refine ⟨16892871491927133848345957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261914327951422565563971 16892871491927133848345957)
                ·
                  refine ⟨3167413404736337596564867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16892871491927133848345957 3167413404736337596564867)
                  ·
                    refine ⟨4751120107104506394847301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167413404736337596564867 4751120107104506394847301)
                    ·
                      refine ⟨890835020082094949033869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4751120107104506394847301 890835020082094949033869)
                      ·
                        rfl

theorem cell23_1734895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_1734895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734895 prefixEnd_1734895 := by exact prefixLift 1734895
  have htrace : WordTrace (prefixWord ++ tailWord_1734895) baseStart_1734895 baseEnd_1734895 := by
    simpa [prefixWord, tailWord_1734895, baseEnd_1734895] using wordTrace_append hprefix tailTrace_1734895
  have hstable : (prefixWord ++ tailWord_1734895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734895).length < 2 ^ (prefixWord ++ tailWord_1734895).sum := by decide
  have hdescent : baseEnd_1734895 < baseStart_1734895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734905 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_1734905 : Nat := 118140960795 + 1734905 * 2 ^ 59
def prefixEnd_1734905 : Nat := 4983230072969 + 3 ^ 40 * 1734905 * 2
def baseEnd_1734905 : Nat := 296946718296213303302941

theorem tailTrace_1734905 : CollatzResearch.WordTrace tailWord_1734905 prefixEnd_1734905 296946718296213303302941 := by
  unfold tailWord_1734905
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277183779742958029606169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42184789186495305353070779 63277183779742958029606169)
  ·
    refine ⟨47457887834807218522204627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63277183779742958029606169 47457887834807218522204627)
    ·
      refine ⟨71186831752210827783306941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47457887834807218522204627 71186831752210827783306941)
      ·
        refine ⟨26695061907079060418740103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71186831752210827783306941 26695061907079060418740103)
        ·
          refine ⟨40042592860618590628110155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26695061907079060418740103 40042592860618590628110155)
          ·
            refine ⟨60063889290927885942165233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40042592860618590628110155 60063889290927885942165233)
            ·
              refine ⟨45047916968195914456623925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60063889290927885942165233 45047916968195914456623925)
              ·
                refine ⟨4223242215768366980308493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45047916968195914456623925 4223242215768366980308493)
                ·
                  refine ⟨1583715830913137617615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4223242215768366980308493 1583715830913137617615685)
                  ·
                    refine ⟨296946718296213303302941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583715830913137617615685 296946718296213303302941)
                    ·
                      rfl

theorem cell23_1734905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_1734905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734905 prefixEnd_1734905 := by exact prefixLift 1734905
  have htrace : WordTrace (prefixWord ++ tailWord_1734905) baseStart_1734905 baseEnd_1734905 := by
    simpa [prefixWord, tailWord_1734905, baseEnd_1734905] using wordTrace_append hprefix tailTrace_1734905
  have hstable : (prefixWord ++ tailWord_1734905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734905).length < 2 ^ (prefixWord ++ tailWord_1734905).sum := by decide
  have hdescent : baseEnd_1734905 < baseStart_1734905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734915 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1734915 : Nat := 118140960795 + 1734915 * 2 ^ 59
def prefixEnd_1734915 : Nat := 4983230072969 + 3 ^ 40 * 1734915 * 2
def baseEnd_1734915 : Nat := 890845289695184870783777

theorem tailTrace_1734915 : CollatzResearch.WordTrace tailWord_1734915 prefixEnd_1734915 890845289695184870783777 := by
  unfold tailWord_1734915
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277548509706729737470199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42185032339804486491646799 63277548509706729737470199)
  ·
    refine ⟨94916322764560094606205299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277548509706729737470199 94916322764560094606205299)
    ·
      refine ⟨142374484146840141909307949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94916322764560094606205299 142374484146840141909307949)
      ·
        refine ⟨53390431555065053215990481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142374484146840141909307949 53390431555065053215990481)
        ·
          refine ⟨40042823666298789911992861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53390431555065053215990481 40042823666298789911992861)
          ·
            refine ⟨15016058874862046216997323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40042823666298789911992861 15016058874862046216997323)
            ·
              refine ⟨22524088312293069325495985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016058874862046216997323 22524088312293069325495985)
              ·
                refine ⟨16893066234219801994121989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524088312293069325495985 16893066234219801994121989)
                ·
                  refine ⟨3167449918916212873897873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16893066234219801994121989 3167449918916212873897873)
                  ·
                    refine ⟨2375587439187159655423405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167449918916212873897873 2375587439187159655423405)
                    ·
                      refine ⟨890845289695184870783777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2375587439187159655423405 890845289695184870783777)
                      ·
                        rfl

theorem cell23_1734915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1734915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734915 prefixEnd_1734915 := by exact prefixLift 1734915
  have htrace : WordTrace (prefixWord ++ tailWord_1734915) baseStart_1734915 baseEnd_1734915 := by
    simpa [prefixWord, tailWord_1734915, baseEnd_1734915] using wordTrace_append hprefix tailTrace_1734915
  have hstable : (prefixWord ++ tailWord_1734915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734915).length < 2 ^ (prefixWord ++ tailWord_1734915).sum := by decide
  have hdescent : baseEnd_1734915 < baseStart_1734915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734965 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1734965 : Nat := 118140960795 + 1734965 * 2 ^ 59
def prefixEnd_1734965 : Nat := 4983230072969 + 3 ^ 40 * 1734965 * 2
def baseEnd_1734965 : Nat := 296956987909303225052849

theorem tailTrace_1734965 : CollatzResearch.WordTrace tailWord_1734965 prefixEnd_1734965 296956987909303225052849 := by
  unfold tailWord_1734965
  simp only [CollatzResearch.WordTrace]
  refine ⟨63279372159525588276790349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42186248106350392184526899 63279372159525588276790349)
  ·
    refine ⟨23729764559822095603796381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63279372159525588276790349 23729764559822095603796381)
    ·
      refine ⟨8898661709933285851423643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23729764559822095603796381 8898661709933285851423643)
      ·
        refine ⟨13347992564899928777135465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898661709933285851423643 13347992564899928777135465)
        ·
          refine ⟨10010994423674946582851599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347992564899928777135465 10010994423674946582851599)
          ·
            refine ⟨15016491635512419874277399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010994423674946582851599 15016491635512419874277399)
            ·
              refine ⟨22524737453268629811416099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016491635512419874277399 22524737453268629811416099)
              ·
                refine ⟨33787106179902944717124149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22524737453268629811416099 33787106179902944717124149)
                ·
                  refine ⟨3167541204365901067230389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33787106179902944717124149 3167541204365901067230389)
                  ·
                    refine ⟨296956987909303225052849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3167541204365901067230389 296956987909303225052849)
                    ·
                      rfl

theorem cell23_1734965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1734965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734965 prefixEnd_1734965 := by exact prefixLift 1734965
  have htrace : WordTrace (prefixWord ++ tailWord_1734965) baseStart_1734965 baseEnd_1734965 := by
    simpa [prefixWord, tailWord_1734965, baseEnd_1734965] using wordTrace_append hprefix tailTrace_1734965
  have hstable : (prefixWord ++ tailWord_1734965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734965).length < 2 ^ (prefixWord ++ tailWord_1734965).sum := by decide
  have hdescent : baseEnd_1734965 < baseStart_1734965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734972 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_1734972 : Nat := 118140960795 + 1734972 * 2 ^ 59
def prefixEnd_1734972 : Nat := 4983230072969 + 3 ^ 40 * 1734972 * 2
def baseEnd_1734972 : Nat := 890874558092491147771015

theorem tailTrace_1734972 : CollatzResearch.WordTrace tailWord_1734972 prefixEnd_1734972 890874558092491147771015 := by
  unfold tailWord_1734972
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639813735250114236147585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42186418313666818981530113 31639813735250114236147585)
  ·
    refine ⟨23729860301437585677110689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31639813735250114236147585 23729860301437585677110689)
    ·
      refine ⟨17797395226078189257833017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23729860301437585677110689 17797395226078189257833017)
      ·
        refine ⟨13348046419558641943374763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17797395226078189257833017 13348046419558641943374763)
        ·
          refine ⟨20022069629337962915062145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348046419558641943374763 20022069629337962915062145)
          ·
            refine ⟨15016552222003472186296609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20022069629337962915062145 15016552222003472186296609)
            ·
              refine ⟨11262414166502604139722457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15016552222003472186296609 11262414166502604139722457)
              ·
                refine ⟨8446810624876953104791843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11262414166502604139722457 8446810624876953104791843)
                ·
                  refine ⟨12670215937315429657187765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8446810624876953104791843 12670215937315429657187765)
                  ·
                    refine ⟨1187832744123321530361353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12670215937315429657187765 1187832744123321530361353)
                    ·
                      refine ⟨890874558092491147771015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187832744123321530361353 890874558092491147771015)
                      ·
                        rfl

theorem cell23_1734972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_1734972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734972 prefixEnd_1734972 := by exact prefixLift 1734972
  have htrace : WordTrace (prefixWord ++ tailWord_1734972) baseStart_1734972 baseEnd_1734972 := by
    simpa [prefixWord, tailWord_1734972, baseEnd_1734972] using wordTrace_append hprefix tailTrace_1734972
  have hstable : (prefixWord ++ tailWord_1734972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734972).length < 2 ^ (prefixWord ++ tailWord_1734972).sum := by decide
  have hdescent : baseEnd_1734972 < baseStart_1734972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734996 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_1734996 : Nat := 118140960795 + 1734996 * 2 ^ 59
def prefixEnd_1734996 : Nat := 4983230072969 + 3 ^ 40 * 1734996 * 2
def baseEnd_1734996 : Nat := 890886881628199053870905

theorem tailTrace_1734996 : CollatzResearch.WordTrace tailWord_1734996 prefixEnd_1734996 890886881628199053870905 := by
  unfold tailWord_1734996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31640251411206640285584421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42187001881608853714112561 31640251411206640285584421)
  ·
    refine ⟨5932547139601245053547079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31640251411206640285584421 5932547139601245053547079)
    ·
      refine ⟨8898820709401867580320619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932547139601245053547079 8898820709401867580320619)
      ·
        refine ⟨13348231064102801370480929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898820709401867580320619 13348231064102801370480929)
        ·
          refine ⟨10011173298077101027860697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13348231064102801370480929 10011173298077101027860697)
          ·
            refine ⟨7508379973557825770895523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011173298077101027860697 7508379973557825770895523)
            ·
              refine ⟨11262569960336738656343285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508379973557825770895523 11262569960336738656343285)
              ·
                refine ⟨1055865933781569249032183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11262569960336738656343285 1055865933781569249032183)
                ·
                  refine ⟨1583798900672353873548275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055865933781569249032183 1583798900672353873548275)
                  ·
                    refine ⟨2375698351008530810322413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1583798900672353873548275 2375698351008530810322413)
                    ·
                      refine ⟨890886881628199053870905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2375698351008530810322413 890886881628199053870905)
                      ·
                        rfl

theorem cell23_1734996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_1734996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1734996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1734996 prefixEnd_1734996 := by exact prefixLift 1734996
  have htrace : WordTrace (prefixWord ++ tailWord_1734996) baseStart_1734996 baseEnd_1734996 := by
    simpa [prefixWord, tailWord_1734996, baseEnd_1734996] using wordTrace_append hprefix tailTrace_1734996
  have hstable : (prefixWord ++ tailWord_1734996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734996).length < 2 ^ (prefixWord ++ tailWord_1734996).sum := by decide
  have hdescent : baseEnd_1734996 < baseStart_1734996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735012 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1735012 : Nat := 118140960795 + 1735012 * 2 ^ 59
def prefixEnd_1735012 : Nat := 4983230072969 + 3 ^ 40 * 1735012 * 2
def baseEnd_1735012 : Nat := 296965032439556997090277

theorem tailTrace_1735012 : CollatzResearch.WordTrace tailWord_1735012 prefixEnd_1735012 296965032439556997090277 := by
  unfold tailWord_1735012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31640543195177657651875645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42187390926903543535834193 31640543195177657651875645)
  ·
    refine ⟨11865203698191621619453367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31640543195177657651875645 11865203698191621619453367)
    ·
      refine ⟨17797805547287432429180051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865203698191621619453367 17797805547287432429180051)
      ·
        refine ⟨26696708320931148643770077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17797805547287432429180051 26696708320931148643770077)
        ·
          refine ⟨10011265620349180741413779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26696708320931148643770077 10011265620349180741413779)
          ·
            refine ⟨15016898430523771112120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011265620349180741413779 15016898430523771112120669)
            ·
              refine ⟨5631336911446414167045251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15016898430523771112120669 5631336911446414167045251)
              ·
                refine ⟨8447005367169621250567877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631336911446414167045251 8447005367169621250567877)
                ·
                  refine ⟨1583813506344303984481477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8447005367169621250567877 1583813506344303984481477)
                  ·
                    refine ⟨296965032439556997090277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583813506344303984481477 296965032439556997090277)
                    ·
                      rfl

theorem cell23_1735012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1735012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735012 prefixEnd_1735012 := by exact prefixLift 1735012
  have htrace : WordTrace (prefixWord ++ tailWord_1735012) baseStart_1735012 baseEnd_1735012 := by
    simpa [prefixWord, tailWord_1735012, baseEnd_1735012] using wordTrace_append hprefix tailTrace_1735012
  have hstable : (prefixWord ++ tailWord_1735012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735012).length < 2 ^ (prefixWord ++ tailWord_1735012).sum := by decide
  have hdescent : baseEnd_1735012 < baseStart_1735012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735029 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1735029 : Nat := 118140960795 + 1735029 * 2 ^ 59
def prefixEnd_1735029 : Nat := 4983230072969 + 3 ^ 40 * 1735029 * 2
def baseEnd_1735029 : Nat := 296967942163265808252751

theorem tailTrace_1735029 : CollatzResearch.WordTrace tailWord_1735029 prefixEnd_1735029 296967942163265808252751 := by
  unfold tailWord_1735029
  simp only [CollatzResearch.WordTrace]
  refine ⟨63281706431293727207120141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42187804287529151471413427 63281706431293727207120141)
  ·
    refine ⟨23730639911735147702670053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63281706431293727207120141 23730639911735147702670053)
    ·
      refine ⟨4449494983450340194250635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23730639911735147702670053 4449494983450340194250635)
      ·
        refine ⟨6674242475175510291375953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449494983450340194250635 6674242475175510291375953)
        ·
          refine ⟨5005681856381632718531965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6674242475175510291375953 5005681856381632718531965)
          ·
            refine ⟨1877130696143112269449487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5005681856381632718531965 1877130696143112269449487)
            ·
              refine ⟨2815696044214668404174231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877130696143112269449487 2815696044214668404174231)
              ·
                refine ⟨4223544066322002606261347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815696044214668404174231 4223544066322002606261347)
                ·
                  refine ⟨6335316099483003909392021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223544066322002606261347 6335316099483003909392021)
                  ·
                    refine ⟨296967942163265808252751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6335316099483003909392021 296967942163265808252751)
                    ·
                      rfl

theorem cell23_1735029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1735029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735029 prefixEnd_1735029 := by exact prefixLift 1735029
  have htrace : WordTrace (prefixWord ++ tailWord_1735029) baseStart_1735029 baseEnd_1735029 := by
    simpa [prefixWord, tailWord_1735029, baseEnd_1735029] using wordTrace_append hprefix tailTrace_1735029
  have hstable : (prefixWord ++ tailWord_1735029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735029).length < 2 ^ (prefixWord ++ tailWord_1735029).sum := by decide
  have hdescent : baseEnd_1735029 < baseStart_1735029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735065 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1735065 : Nat := 118140960795 + 1735065 * 2 ^ 59
def prefixEnd_1735065 : Nat := 4983230072969 + 3 ^ 40 * 1735065 * 2
def baseEnd_1735065 : Nat := 890922311793359283908087

theorem tailTrace_1735065 : CollatzResearch.WordTrace tailWord_1735065 prefixEnd_1735065 890922311793359283908087 := by
  unfold tailWord_1735065
  simp only [CollatzResearch.WordTrace]
  refine ⟨63283019459163305355430649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42188679639442203570287099 63283019459163305355430649)
  ·
    refine ⟨47462264594372479016572987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63283019459163305355430649 47462264594372479016572987)
    ·
      refine ⟨71193396891558718524859481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47462264594372479016572987 71193396891558718524859481)
      ·
        refine ⟨53395047668669038893644611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71193396891558718524859481 53395047668669038893644611)
        ·
          refine ⟨80092571503003558340466917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53395047668669038893644611 80092571503003558340466917)
          ·
            refine ⟨15017357156813167188837547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80092571503003558340466917 15017357156813167188837547)
            ·
              refine ⟨22526035735219750783256321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15017357156813167188837547 22526035735219750783256321)
              ·
                refine ⟨16894526801414813087442241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22526035735219750783256321 16894526801414813087442241)
                ·
                  refine ⟨12670895101061109815581681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16894526801414813087442241 12670895101061109815581681)
                  ·
                    refine ⟨9503171325795832361686261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12670895101061109815581681 9503171325795832361686261)
                    ·
                      refine ⟨890922311793359283908087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9503171325795832361686261 890922311793359283908087)
                      ·
                        rfl

theorem cell23_1735065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1735065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735065 prefixEnd_1735065 := by exact prefixLift 1735065
  have htrace : WordTrace (prefixWord ++ tailWord_1735065) baseStart_1735065 baseEnd_1735065 := by
    simpa [prefixWord, tailWord_1735065, baseEnd_1735065] using wordTrace_append hprefix tailTrace_1735065
  have hstable : (prefixWord ++ tailWord_1735065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735065).length < 2 ^ (prefixWord ++ tailWord_1735065).sum := by decide
  have hdescent : baseEnd_1735065 < baseStart_1735065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735070 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1735070 : Nat := 118140960795 + 1735070 * 2 ^ 59
def prefixEnd_1735070 : Nat := 4983230072969 + 3 ^ 40 * 1735070 * 2
def baseEnd_1735070 : Nat := 890924879196631764345565

theorem tailTrace_1735070 : CollatzResearch.WordTrace tailWord_1735070 prefixEnd_1735070 890924879196631764345565 := by
  unfold tailWord_1735070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910400228018148901170333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42188801216096794139575109 7910400228018148901170333)
  ·
    refine ⟨2966400085506805837938875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7910400228018148901170333 2966400085506805837938875)
    ·
      refine ⟨4449600128260208756908313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966400085506805837938875 4449600128260208756908313)
      ·
        refine ⟨3337200096195156567681235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449600128260208756908313 3337200096195156567681235)
        ·
          refine ⟨5005800144292734851521853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337200096195156567681235 5005800144292734851521853)
          ·
            refine ⟨1877175054109775569320695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5005800144292734851521853 1877175054109775569320695)
            ·
              refine ⟨2815762581164663353981043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877175054109775569320695 2815762581164663353981043)
              ·
                refine ⟨4223643871746995030971565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815762581164663353981043 4223643871746995030971565)
                ·
                  refine ⟨1583866451905123136614337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4223643871746995030971565 1583866451905123136614337)
                  ·
                    refine ⟨1187899838928842352460753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1583866451905123136614337 1187899838928842352460753)
                    ·
                      refine ⟨890924879196631764345565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187899838928842352460753 890924879196631764345565)
                      ·
                        rfl

theorem cell23_1735070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1735070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735070 prefixEnd_1735070 := by exact prefixLift 1735070
  have htrace : WordTrace (prefixWord ++ tailWord_1735070) baseStart_1735070 baseEnd_1735070 := by
    simpa [prefixWord, tailWord_1735070, baseEnd_1735070] using wordTrace_append hprefix tailTrace_1735070
  have hstable : (prefixWord ++ tailWord_1735070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735070).length < 2 ^ (prefixWord ++ tailWord_1735070).sum := by decide
  have hdescent : baseEnd_1735070 < baseStart_1735070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735112 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1735112 : Nat := 118140960795 + 1735112 * 2 ^ 59
def prefixEnd_1735112 : Nat := 4983230072969 + 3 ^ 40 * 1735112 * 2
def baseEnd_1735112 : Nat := 890946445384120600020371

theorem tailTrace_1735112 : CollatzResearch.WordTrace tailWord_1735112 prefixEnd_1735112 890946445384120600020371 := by
  unfold tailWord_1735112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31642366844996516191195795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42189822459995354921594393 31642366844996516191195795)
  ·
    refine ⟨47463550267494774286793693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31642366844996516191195795 47463550267494774286793693)
    ·
      refine ⟨17798831350310540357547635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47463550267494774286793693 17798831350310540357547635)
      ·
        refine ⟨26698247025465810536321453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17798831350310540357547635 26698247025465810536321453)
        ·
          refine ⟨10011842634549678951120545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26698247025465810536321453 10011842634549678951120545)
          ·
            refine ⟨7508881975912259213340409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011842634549678951120545 7508881975912259213340409)
            ·
              refine ⟨5631661481934194410005307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508881975912259213340409 5631661481934194410005307)
              ·
                refine ⟨8447492222901291615007961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631661481934194410005307 8447492222901291615007961)
                ·
                  refine ⟨6335619167175968711255971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447492222901291615007961 6335619167175968711255971)
                  ·
                    refine ⟨9503428750763953066883957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6335619167175968711255971 9503428750763953066883957)
                    ·
                      refine ⟨890946445384120600020371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9503428750763953066883957 890946445384120600020371)
                      ·
                        rfl

theorem cell23_1735112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1735112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735112 prefixEnd_1735112 := by exact prefixLift 1735112
  have htrace : WordTrace (prefixWord ++ tailWord_1735112) baseStart_1735112 baseEnd_1735112 := by
    simpa [prefixWord, tailWord_1735112, baseEnd_1735112] using wordTrace_append hprefix tailTrace_1735112
  have hstable : (prefixWord ++ tailWord_1735112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735112).length < 2 ^ (prefixWord ++ tailWord_1735112).sum := by decide
  have hdescent : baseEnd_1735112 < baseStart_1735112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735126 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1735126 : Nat := 118140960795 + 1735126 * 2 ^ 59
def prefixEnd_1735126 : Nat := 4983230072969 + 3 ^ 40 * 1735126 * 2
def baseEnd_1735126 : Nat := 890953634113283545245307

theorem tailTrace_1735126 : CollatzResearch.WordTrace tailWord_1735126 prefixEnd_1735126 890953634113283545245307 := by
  unfold tailWord_1735126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955327769496394548337577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42190162874628208515600821 3955327769496394548337577)
  ·
    refine ⟨2966495827122295911253183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955327769496394548337577 2966495827122295911253183)
    ·
      refine ⟨4449743740683443866879775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966495827122295911253183 4449743740683443866879775)
      ·
        refine ⟨6674615611025165800319663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449743740683443866879775 6674615611025165800319663)
        ·
          refine ⟨10011923416537748700479495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674615611025165800319663 10011923416537748700479495)
          ·
            refine ⟨15017885124806623050719243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011923416537748700479495 15017885124806623050719243)
            ·
              refine ⟨22526827687209934576078865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15017885124806623050719243 22526827687209934576078865)
              ·
                refine ⟨16895120765407450932059149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22526827687209934576078865 16895120765407450932059149)
                ·
                  refine ⟨6335670287027794099522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16895120765407450932059149 6335670287027794099522181)
                  ·
                    refine ⟨1187938178817711393660409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6335670287027794099522181 1187938178817711393660409)
                    ·
                      refine ⟨890953634113283545245307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1187938178817711393660409 890953634113283545245307)
                      ·
                        rfl

theorem cell23_1735126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1735126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735126 prefixEnd_1735126 := by exact prefixLift 1735126
  have htrace : WordTrace (prefixWord ++ tailWord_1735126) baseStart_1735126 baseEnd_1735126 := by
    simpa [prefixWord, tailWord_1735126, baseEnd_1735126] using wordTrace_append hprefix tailTrace_1735126
  have hstable : (prefixWord ++ tailWord_1735126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735126).length < 2 ^ (prefixWord ++ tailWord_1735126).sum := by decide
  have hdescent : baseEnd_1735126 < baseStart_1735126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735139 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1735139 : Nat := 118140960795 + 1735139 * 2 ^ 59
def prefixEnd_1735139 : Nat := 4983230072969 + 3 ^ 40 * 1735139 * 2
def baseEnd_1735139 : Nat := 890960309361791994382747

theorem tailTrace_1735139 : CollatzResearch.WordTrace tailWord_1735139 prefixEnd_1735139 890960309361791994382747 := by
  unfold tailWord_1735139
  simp only [CollatzResearch.WordTrace]
  refine ⟨63285718460895215993624471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42190478973930143995749647 63285718460895215993624471)
  ·
    refine ⟨94928577691342823990436707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63285718460895215993624471 94928577691342823990436707)
    ·
      refine ⟨142392866537014235985655061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94928577691342823990436707 142392866537014235985655061)
      ·
        refine ⟨6674665618922542311827581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142392866537014235985655061 6674665618922542311827581)
        ·
          refine ⟨2502999607095953366935343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6674665618922542311827581 2502999607095953366935343)
          ·
            refine ⟨3754499410643930050403015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502999607095953366935343 3754499410643930050403015)
            ·
              refine ⟨5631749115965895075604523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754499410643930050403015 5631749115965895075604523)
              ·
                refine ⟨8447623673948842613406785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631749115965895075604523 8447623673948842613406785)
                ·
                  refine ⟨6335717755461631960055089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447623673948842613406785 6335717755461631960055089)
                  ·
                    refine ⟨4751788316596223970041317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6335717755461631960055089 4751788316596223970041317)
                    ·
                      refine ⟨890960309361791994382747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4751788316596223970041317 890960309361791994382747)
                      ·
                        rfl

theorem cell23_1735139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1735139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735139 prefixEnd_1735139 := by exact prefixLift 1735139
  have htrace : WordTrace (prefixWord ++ tailWord_1735139) baseStart_1735139 baseEnd_1735139 := by
    simpa [prefixWord, tailWord_1735139, baseEnd_1735139] using wordTrace_append hprefix tailTrace_1735139
  have hstable : (prefixWord ++ tailWord_1735139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735139).length < 2 ^ (prefixWord ++ tailWord_1735139).sum := by decide
  have hdescent : baseEnd_1735139 < baseStart_1735139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735149 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1735149 : Nat := 118140960795 + 1735149 * 2 ^ 59
def prefixEnd_1735149 : Nat := 4983230072969 + 3 ^ 40 * 1735149 * 2
def baseEnd_1735149 : Nat := 98996160463148550584189

theorem tailTrace_1735149 : CollatzResearch.WordTrace tailWord_1735149 prefixEnd_1735149 98996160463148550584189 := by
  unfold tailWord_1735149
  simp only [CollatzResearch.WordTrace]
  refine ⟨63286083190858987701488501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42190722127239325134325667 63286083190858987701488501)
  ·
    refine ⟨5933070299143030097014547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63286083190858987701488501 5933070299143030097014547)
    ·
      refine ⟨8899605448714545145521821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5933070299143030097014547 8899605448714545145521821)
      ·
        refine ⟨3337352043267954429570683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8899605448714545145521821 3337352043267954429570683)
        ·
          refine ⟨5006028064901931644356025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337352043267954429570683 5006028064901931644356025)
          ·
            refine ⟨3754521048676448733267019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006028064901931644356025 3754521048676448733267019)
            ·
              refine ⟨5631781573014673099900529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754521048676448733267019 5631781573014673099900529)
              ·
                refine ⟨4223836179761004824925397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5631781573014673099900529 4223836179761004824925397)
                ·
                  refine ⟨98996160463148550584189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4223836179761004824925397 98996160463148550584189)
                  ·
                    rfl

theorem cell23_1735149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1735149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735149 prefixEnd_1735149 := by exact prefixLift 1735149
  have htrace : WordTrace (prefixWord ++ tailWord_1735149) baseStart_1735149 baseEnd_1735149 := by
    simpa [prefixWord, tailWord_1735149, baseEnd_1735149] using wordTrace_append hprefix tailTrace_1735149
  have hstable : (prefixWord ++ tailWord_1735149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735149).length < 2 ^ (prefixWord ++ tailWord_1735149).sum := by decide
  have hdescent : baseEnd_1735149 < baseStart_1735149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735162 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_1735162 : Nat := 118140960795 + 1735162 * 2 ^ 59
def prefixEnd_1735162 : Nat := 4983230072969 + 3 ^ 40 * 1735162 * 2
def baseEnd_1735162 : Nat := 296990706472281801465047

theorem tailTrace_1735162 : CollatzResearch.WordTrace tailWord_1735162 prefixEnd_1735162 296990706472281801465047 := by
  unfold tailWord_1735162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821639334952972730427935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42191038226541260614474493 15821639334952972730427935)
  ·
    refine ⟨23732459002429459095641903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15821639334952972730427935 23732459002429459095641903)
    ·
      refine ⟨35598688503644188643462855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732459002429459095641903 35598688503644188643462855)
      ·
        refine ⟨53398032755466282965194283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35598688503644188643462855 53398032755466282965194283)
        ·
          refine ⟨80097049133199424447791425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53398032755466282965194283 80097049133199424447791425)
          ·
            refine ⟨60072786849899568335843569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80097049133199424447791425 60072786849899568335843569)
            ·
              refine ⟨45054590137424676251882677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60072786849899568335843569 45054590137424676251882677)
              ·
                refine ⟨4223867825383563398614001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45054590137424676251882677 4223867825383563398614001)
                ·
                  refine ⟨3167900869037672548960501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223867825383563398614001 3167900869037672548960501)
                  ·
                    refine ⟨296990706472281801465047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3167900869037672548960501 296990706472281801465047)
                    ·
                      rfl

theorem cell23_1735162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_1735162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735162 prefixEnd_1735162 := by exact prefixLift 1735162
  have htrace : WordTrace (prefixWord ++ tailWord_1735162) baseStart_1735162 baseEnd_1735162 := by
    simpa [prefixWord, tailWord_1735162, baseEnd_1735162] using wordTrace_append hprefix tailTrace_1735162
  have hstable : (prefixWord ++ tailWord_1735162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735162).length < 2 ^ (prefixWord ++ tailWord_1735162).sum := by decide
  have hdescent : baseEnd_1735162 < baseStart_1735162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735219 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3]
def baseStart_1735219 : Nat := 118140960795 + 1735219 * 2 ^ 59
def prefixEnd_1735219 : Nat := 4983230072969 + 3 ^ 40 * 1735219 * 2
def baseEnd_1735219 : Nat := 891001387814151681382379

theorem tailTrace_1735219 : CollatzResearch.WordTrace tailWord_1735219 prefixEnd_1735219 891001387814151681382379 := by
  unfold tailWord_1735219
  simp only [CollatzResearch.WordTrace]
  refine ⟨63288636300605389656536711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42192424200403593104357807 63288636300605389656536711)
  ·
    refine ⟨94932954450908084484805067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63288636300605389656536711 94932954450908084484805067)
    ·
      refine ⟨142399431676362126727207601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94932954450908084484805067 142399431676362126727207601)
      ·
        refine ⟨106799573757271595045405701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142399431676362126727207601 106799573757271595045405701)
        ·
          refine ⟨20024920079488424071013569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106799573757271595045405701 20024920079488424071013569)
          ·
            refine ⟨15018690059616318053260177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20024920079488424071013569 15018690059616318053260177)
            ·
              refine ⟨11264017544712238539945133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15018690059616318053260177 11264017544712238539945133)
              ·
                refine ⟨4224006579267089452479425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11264017544712238539945133 4224006579267089452479425)
                ·
                  refine ⟨3168004934450317089359569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224006579267089452479425 3168004934450317089359569)
                  ·
                    refine ⟨2376003700837737817019677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168004934450317089359569 2376003700837737817019677)
                    ·
                      refine ⟨891001387814151681382379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376003700837737817019677 891001387814151681382379)
                      ·
                        rfl

theorem cell23_1735219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_1735219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735219 prefixEnd_1735219 := by exact prefixLift 1735219
  have htrace : WordTrace (prefixWord ++ tailWord_1735219) baseStart_1735219 baseEnd_1735219 := by
    simpa [prefixWord, tailWord_1735219, baseEnd_1735219] using wordTrace_append hprefix tailTrace_1735219
  have hstable : (prefixWord ++ tailWord_1735219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735219).length < 2 ^ (prefixWord ++ tailWord_1735219).sum := by decide
  have hdescent : baseEnd_1735219 < baseStart_1735219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735276 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_1735276 : Nat := 118140960795 + 1735276 * 2 ^ 59
def prefixEnd_1735276 : Nat := 4983230072969 + 3 ^ 40 * 1735276 * 2
def baseEnd_1735276 : Nat := 891030656211457958369617

theorem tailTrace_1735276 : CollatzResearch.WordTrace tailWord_1735276 prefixEnd_1735276 891030656211457958369617 := by
  unfold tailWord_1735276
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645357630699444195680841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42193810174265925594241121 31645357630699444195680841)
  ·
    refine ⟨23734018223024583146760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31645357630699444195680841 23734018223024583146760631)
    ·
      refine ⟨35601027334536874720140947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23734018223024583146760631 35601027334536874720140947)
      ·
        refine ⟨53401541001805312080211421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35601027334536874720140947 53401541001805312080211421)
        ·
          refine ⟨20025577875676992030079283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53401541001805312080211421 20025577875676992030079283)
          ·
            refine ⟨30038366813515488045118925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20025577875676992030079283 30038366813515488045118925)
            ·
              refine ⟨11264387555068308016919597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30038366813515488045118925 11264387555068308016919597)
              ·
                refine ⟨4224145333150615506344849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11264387555068308016919597 4224145333150615506344849)
                ·
                  refine ⟨3168108999862961629758637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224145333150615506344849 3168108999862961629758637)
                  ·
                    refine ⟨1188040874948610611159489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168108999862961629758637 1188040874948610611159489)
                    ·
                      refine ⟨891030656211457958369617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188040874948610611159489 891030656211457958369617)
                      ·
                        rfl

theorem cell23_1735276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_1735276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735276 prefixEnd_1735276 := by exact prefixLift 1735276
  have htrace : WordTrace (prefixWord ++ tailWord_1735276) baseStart_1735276 baseEnd_1735276 := by
    simpa [prefixWord, tailWord_1735276, baseEnd_1735276] using wordTrace_append hprefix tailTrace_1735276
  have hstable : (prefixWord ++ tailWord_1735276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735276).length < 2 ^ (prefixWord ++ tailWord_1735276).sum := by decide
  have hdescent : baseEnd_1735276 < baseStart_1735276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735299 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 4, 4]
def baseStart_1735299 : Nat := 118140960795 + 1735299 * 2 ^ 59
def prefixEnd_1735299 : Nat := 4983230072969 + 3 ^ 40 * 1735299 * 2
def baseEnd_1735299 : Nat := 297014155422170456127337

theorem tailTrace_1735299 : CollatzResearch.WordTrace tailWord_1735299 prefixEnd_1735299 297014155422170456127337 := by
  unfold tailWord_1735299
  simp only [CollatzResearch.WordTrace]
  refine ⟨63291554140315563319448951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42194369426877042212965967 63291554140315563319448951)
  ·
    refine ⟨94937331210473344979173427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63291554140315563319448951 94937331210473344979173427)
    ·
      refine ⟨142405996815710017468760141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94937331210473344979173427 142405996815710017468760141)
      ·
        refine ⟨53402248805891256550785053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142405996815710017468760141 53402248805891256550785053)
        ·
          refine ⟨20025843302209221206544395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53402248805891256550785053 20025843302209221206544395)
          ·
            refine ⟨30038764953313831809816593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20025843302209221206544395 30038764953313831809816593)
            ·
              refine ⟨22529073714985373857362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30038764953313831809816593 22529073714985373857362445)
              ·
                refine ⟨8448402643119515196510917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22529073714985373857362445 8448402643119515196510917)
                ·
                  refine ⟨1584075495584909099345797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8448402643119515196510917 1584075495584909099345797)
                  ·
                    refine ⟨297014155422170456127337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584075495584909099345797 297014155422170456127337)
                    ·
                      rfl

theorem cell23_1735299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 4].length) (baseStart_1735299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735299 prefixEnd_1735299 := by exact prefixLift 1735299
  have htrace : WordTrace (prefixWord ++ tailWord_1735299) baseStart_1735299 baseEnd_1735299 := by
    simpa [prefixWord, tailWord_1735299, baseEnd_1735299] using wordTrace_append hprefix tailTrace_1735299
  have hstable : (prefixWord ++ tailWord_1735299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735299).length < 2 ^ (prefixWord ++ tailWord_1735299).sum := by decide
  have hdescent : baseEnd_1735299 < baseStart_1735299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735300 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1735300 : Nat := 118140960795 + 1735300 * 2 ^ 59
def prefixEnd_1735300 : Nat := 4983230072969 + 3 ^ 40 * 1735300 * 2
def baseEnd_1735300 : Nat := 891042979747165864469507

theorem tailTrace_1735300 : CollatzResearch.WordTrace tailWord_1735300 prefixEnd_1735300 891042979747165864469507 := by
  unfold tailWord_1735300
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645795306655970245117677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42194393742207960326823569 31645795306655970245117677)
  ·
    refine ⟨11867173239995988841919129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31645795306655970245117677 11867173239995988841919129)
    ·
      refine ⟨8900379929996991631439347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11867173239995988841919129 8900379929996991631439347)
      ·
        refine ⟨13350569894995487447159021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8900379929996991631439347 13350569894995487447159021)
        ·
          refine ⟨5006463710623307792684633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13350569894995487447159021 5006463710623307792684633)
          ·
            refine ⟨3754847782967480844513475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006463710623307792684633 3754847782967480844513475)
            ·
              refine ⟨5632271674451221266770213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754847782967480844513475 5632271674451221266770213)
              ·
                refine ⟨1056050938959603987519415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5632271674451221266770213 1056050938959603987519415)
                ·
                  refine ⟨1584076408439405981279123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056050938959603987519415 1584076408439405981279123)
                  ·
                    refine ⟨2376114612659108971918685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584076408439405981279123 2376114612659108971918685)
                    ·
                      refine ⟨891042979747165864469507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376114612659108971918685 891042979747165864469507)
                      ·
                        rfl

theorem cell23_1735300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1735300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735300 prefixEnd_1735300 := by exact prefixLift 1735300
  have htrace : WordTrace (prefixWord ++ tailWord_1735300) baseStart_1735300 baseEnd_1735300 := by
    simpa [prefixWord, tailWord_1735300, baseEnd_1735300] using wordTrace_append hprefix tailTrace_1735300
  have hstable : (prefixWord ++ tailWord_1735300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735300).length < 2 ^ (prefixWord ++ tailWord_1735300).sum := by decide
  have hdescent : baseEnd_1735300 < baseStart_1735300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735316 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1735316 : Nat := 118140960795 + 1735316 * 2 ^ 59
def prefixEnd_1735316 : Nat := 4983230072969 + 3 ^ 40 * 1735316 * 2
def baseEnd_1735316 : Nat := 297017065145879267289811

theorem tailTrace_1735316 : CollatzResearch.WordTrace tailWord_1735316 prefixEnd_1735316 297017065145879267289811 := by
  unfold tailWord_1735316
  simp only [CollatzResearch.WordTrace]
  refine ⟨31646087090626987611408901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42194782787502650148545201 31646087090626987611408901)
  ·
    refine ⟨5933641329492560177139169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31646087090626987611408901 5933641329492560177139169)
    ·
      refine ⟨4450230997119420132854377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5933641329492560177139169 4450230997119420132854377)
      ·
        refine ⟨3337673247839565099640783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450230997119420132854377 3337673247839565099640783)
        ·
          refine ⟨5006509871759347649461175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337673247839565099640783 5006509871759347649461175)
          ·
            refine ⟨7509764807639021474191763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006509871759347649461175 7509764807639021474191763)
            ·
              refine ⟨11264647211458532211287645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509764807639021474191763 11264647211458532211287645)
              ·
                refine ⟨4224242704296949579232867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11264647211458532211287645 4224242704296949579232867)
                ·
                  refine ⟨6336364056445424368849301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224242704296949579232867 6336364056445424368849301)
                  ·
                    refine ⟨297017065145879267289811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6336364056445424368849301 297017065145879267289811)
                    ·
                      rfl

theorem cell23_1735316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1735316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735316 prefixEnd_1735316 := by exact prefixLift 1735316
  have htrace : WordTrace (prefixWord ++ tailWord_1735316) baseStart_1735316 baseEnd_1735316 := by
    simpa [prefixWord, tailWord_1735316, baseEnd_1735316] using wordTrace_append hprefix tailTrace_1735316
  have hstable : (prefixWord ++ tailWord_1735316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735316).length < 2 ^ (prefixWord ++ tailWord_1735316).sum := by decide
  have hdescent : baseEnd_1735316 < baseStart_1735316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735343 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 1, 2, 3]
def baseStart_1735343 : Nat := 118140960795 + 1735343 * 2 ^ 59
def prefixEnd_1735343 : Nat := 4983230072969 + 3 ^ 40 * 1735343 * 2
def baseEnd_1735343 : Nat := 891065059415309196231809

theorem tailTrace_1735343 : CollatzResearch.WordTrace tailWord_1735343 prefixEnd_1735343 891065059415309196231809 := by
  unfold tailWord_1735343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63293158952156158834050683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42195439301437439222700455 63293158952156158834050683)
  ·
    refine ⟨94939738428234238251076025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63293158952156158834050683 94939738428234238251076025)
    ·
      refine ⟨71204803821175678688307019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94939738428234238251076025 71204803821175678688307019)
      ·
        refine ⟨106807205731763518032460529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71204803821175678688307019 106807205731763518032460529)
        ·
          refine ⟨80105404298822638524345397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106807205731763518032460529 80105404298822638524345397)
          ·
            refine ⟨7509881653014622361657381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80105404298822638524345397 7509881653014622361657381)
            ·
              refine ⟨1408102809940241692810759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7509881653014622361657381 1408102809940241692810759)
              ·
                refine ⟨2112154214910362539216139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408102809940241692810759 2112154214910362539216139)
                ·
                  refine ⟨3168231322365543808824209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112154214910362539216139 3168231322365543808824209)
                  ·
                    refine ⟨2376173491774157856618157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168231322365543808824209 2376173491774157856618157)
                    ·
                      refine ⟨891065059415309196231809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376173491774157856618157 891065059415309196231809)
                      ·
                        rfl

theorem cell23_1735343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 2, 3].length) (baseStart_1735343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735343 prefixEnd_1735343 := by exact prefixLift 1735343
  have htrace : WordTrace (prefixWord ++ tailWord_1735343) baseStart_1735343 baseEnd_1735343 := by
    simpa [prefixWord, tailWord_1735343, baseEnd_1735343] using wordTrace_append hprefix tailTrace_1735343
  have hstable : (prefixWord ++ tailWord_1735343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735343).length < 2 ^ (prefixWord ++ tailWord_1735343).sum := by decide
  have hdescent : baseEnd_1735343 < baseStart_1735343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735350 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1735350 : Nat := 118140960795 + 1735350 * 2 ^ 59
def prefixEnd_1735350 : Nat := 4983230072969 + 3 ^ 40 * 1735350 * 2
def baseEnd_1735350 : Nat := 297022884593296889614759

theorem tailTrace_1735350 : CollatzResearch.WordTrace tailWord_1735350 prefixEnd_1735350 297022884593296889614759 := by
  unfold tailWord_1735350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955838391445674939347219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42195609508753866019703669 3955838391445674939347219)
  ·
    refine ⟨5933757587168512409020829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3955838391445674939347219 5933757587168512409020829)
    ·
      refine ⟨2225159095188192153382811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5933757587168512409020829 2225159095188192153382811)
      ·
        refine ⟨3337738642782288230074217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225159095188192153382811 3337738642782288230074217)
        ·
          refine ⟨2503303982086716172555663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337738642782288230074217 2503303982086716172555663)
          ·
            refine ⟨3754955973130074258833495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503303982086716172555663 3754955973130074258833495)
            ·
              refine ⟨5632433959695111388250243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754955973130074258833495 5632433959695111388250243)
              ·
                refine ⟨8448650939542667082375365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632433959695111388250243 8448650939542667082375365)
                ·
                  refine ⟨1584122051164250077945381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8448650939542667082375365 1584122051164250077945381)
                  ·
                    refine ⟨297022884593296889614759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584122051164250077945381 297022884593296889614759)
                    ·
                      rfl

theorem cell23_1735350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1735350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735350 prefixEnd_1735350 := by exact prefixLift 1735350
  have htrace : WordTrace (prefixWord ++ tailWord_1735350) baseStart_1735350 baseEnd_1735350 := by
    simpa [prefixWord, tailWord_1735350, baseEnd_1735350] using wordTrace_append hprefix tailTrace_1735350
  have hstable : (prefixWord ++ tailWord_1735350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735350).length < 2 ^ (prefixWord ++ tailWord_1735350).sum := by decide
  have hdescent : baseEnd_1735350 < baseStart_1735350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735380 : List Nat := [2, 4, 1, 3, 3, 1, 2, 7]
def baseStart_1735380 : Nat := 118140960795 + 1735380 * 2 ^ 59
def prefixEnd_1735380 : Nat := 4983230072969 + 3 ^ 40 * 1735380 * 2
def baseEnd_1735380 : Nat := 33003113266649094498857

theorem tailTrace_1735380 : CollatzResearch.WordTrace tailWord_1735380 prefixEnd_1735380 33003113266649094498857 := by
  unfold tailWord_1735380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31647254226511057076573797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42196338968681409435431729 31647254226511057076573797)
  ·
    refine ⟨5933860167470823201857587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31647254226511057076573797 5933860167470823201857587)
    ·
      refine ⟨8900790251206234802786381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5933860167470823201857587 8900790251206234802786381)
      ·
        refine ⟨3337796344202338051044893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8900790251206234802786381 3337796344202338051044893)
        ·
          refine ⟨1251673629075876769141835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3337796344202338051044893 1251673629075876769141835)
          ·
            refine ⟨1877510443613815153712753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251673629075876769141835 1877510443613815153712753)
            ·
              refine ⟨1408132832710361365284565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877510443613815153712753 1408132832710361365284565)
              ·
                refine ⟨33003113266649094498857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1408132832710361365284565 33003113266649094498857)
                ·
                  rfl

theorem cell23_1735380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 7].length) (baseStart_1735380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735380 prefixEnd_1735380 := by exact prefixLift 1735380
  have htrace : WordTrace (prefixWord ++ tailWord_1735380) baseStart_1735380 baseEnd_1735380 := by
    simpa [prefixWord, tailWord_1735380, baseEnd_1735380] using wordTrace_append hprefix tailTrace_1735380
  have hstable : (prefixWord ++ tailWord_1735380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735380).length < 2 ^ (prefixWord ++ tailWord_1735380).sum := by decide
  have hdescent : baseEnd_1735380 < baseStart_1735380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735383 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_1735383 : Nat := 118140960795 + 1735383 * 2 ^ 59
def prefixEnd_1735383 : Nat := 4983230072969 + 3 ^ 40 * 1735383 * 2
def baseEnd_1735383 : Nat := 891085598641489039731625

theorem tailTrace_1735383 : CollatzResearch.WordTrace tailWord_1735383 prefixEnd_1735383 891085598641489039731625 := by
  unfold tailWord_1735383
  simp only [CollatzResearch.WordTrace]
  refine ⟨63294617872011245665506803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42196411914674163777004535 63294617872011245665506803)
  ·
    refine ⟨94941926808016868498260205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63294617872011245665506803 94941926808016868498260205)
    ·
      refine ⟨35603222553006325686847577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94941926808016868498260205 35603222553006325686847577)
      ·
        refine ⟨26702416914754744265135683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35603222553006325686847577 26702416914754744265135683)
        ·
          refine ⟨40053625372132116397703525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26702416914754744265135683 40053625372132116397703525)
          ·
            refine ⟨7510054757274771824569411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40053625372132116397703525 7510054757274771824569411)
            ·
              refine ⟨11265082135912157736854117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510054757274771824569411 11265082135912157736854117)
              ·
                refine ⟨2112202900483529575660147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11265082135912157736854117 2112202900483529575660147)
                ·
                  refine ⟨3168304350725294363490221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112202900483529575660147 3168304350725294363490221)
                  ·
                    refine ⟨1188114131521985386308833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168304350725294363490221 1188114131521985386308833)
                    ·
                      refine ⟨891085598641489039731625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188114131521985386308833 891085598641489039731625)
                      ·
                        rfl

theorem cell23_1735383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_1735383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735383 prefixEnd_1735383 := by exact prefixLift 1735383
  have htrace : WordTrace (prefixWord ++ tailWord_1735383) baseStart_1735383 baseEnd_1735383 := by
    simpa [prefixWord, tailWord_1735383, baseEnd_1735383] using wordTrace_append hprefix tailTrace_1735383
  have hstable : (prefixWord ++ tailWord_1735383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735383).length < 2 ^ (prefixWord ++ tailWord_1735383).sum := by decide
  have hdescent : baseEnd_1735383 < baseStart_1735383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735470 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_1735470 : Nat := 118140960795 + 1735470 * 2 ^ 59
def prefixEnd_1735470 : Nat := 4983230072969 + 3 ^ 40 * 1735470 * 2
def baseEnd_1735470 : Nat := 99014474606492244371525

theorem tailTrace_1735470 : CollatzResearch.WordTrace tailWord_1735470 prefixEnd_1735470 99014474606492244371525 := by
  unfold tailWord_1735470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912223877837007440490483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42198527348464039682615909 7912223877837007440490483)
  ·
    refine ⟨11868335816755511160735725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7912223877837007440490483 11868335816755511160735725)
    ·
      refine ⟨4450625931283316685275897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11868335816755511160735725 4450625931283316685275897)
      ·
        refine ⟨3337969448462487513956923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450625931283316685275897 3337969448462487513956923)
        ·
          refine ⟨5006954172693731270935385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337969448462487513956923 5006954172693731270935385)
          ·
            refine ⟨3755215629520298453201539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006954172693731270935385 3755215629520298453201539)
            ·
              refine ⟨5632823444280447679802309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755215629520298453201539 5632823444280447679802309)
              ·
                refine ⟨1056154395802583939962933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5632823444280447679802309 1056154395802583939962933)
                ·
                  refine ⟨99014474606492244371525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056154395802583939962933 99014474606492244371525)
                  ·
                    rfl

theorem cell23_1735470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_1735470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735470 prefixEnd_1735470 := by exact prefixLift 1735470
  have htrace : WordTrace (prefixWord ++ tailWord_1735470) baseStart_1735470 baseEnd_1735470 := by
    simpa [prefixWord, tailWord_1735470, baseEnd_1735470] using wordTrace_append hprefix tailTrace_1735470
  have hstable : (prefixWord ++ tailWord_1735470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735470).length < 2 ^ (prefixWord ++ tailWord_1735470).sum := by decide
  have hdescent : baseEnd_1735470 < baseStart_1735470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735499 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_1735499 : Nat := 118140960795 + 1735499 * 2 ^ 59
def prefixEnd_1735499 : Nat := 4983230072969 + 3 ^ 40 * 1735499 * 2
def baseEnd_1735499 : Nat := 891145162397410585881091

theorem tailTrace_1735499 : CollatzResearch.WordTrace tailWord_1735499 prefixEnd_1735499 891145162397410585881091 := by
  unfold tailWord_1735499
  simp only [CollatzResearch.WordTrace]
  refine ⟨63298848739590997476729551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42199232493060664984486367 63298848739590997476729551)
  ·
    refine ⟨94948273109386496215094327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63298848739590997476729551 94948273109386496215094327)
    ·
      refine ⟨142422409664079744322641491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94948273109386496215094327 142422409664079744322641491)
      ·
        refine ⟨213633614496119616483962237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142422409664079744322641491 213633614496119616483962237)
        ·
          refine ⟨80112605436044856181485839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213633614496119616483962237 80112605436044856181485839)
          ·
            refine ⟨120168908154067284272228759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80112605436044856181485839 120168908154067284272228759)
            ·
              refine ⟨180253362231100926408343139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120168908154067284272228759 180253362231100926408343139)
              ·
                refine ⟨270380043346651389612514709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180253362231100926408343139 270380043346651389612514709)
                ·
                  refine ⟨12674064531874283888086627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270380043346651389612514709 12674064531874283888086627)
                  ·
                    refine ⟨19011096797811425832129941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12674064531874283888086627 19011096797811425832129941)
                    ·
                      refine ⟨891145162397410585881091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19011096797811425832129941 891145162397410585881091)
                      ·
                        rfl

theorem cell23_1735499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_1735499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735499 prefixEnd_1735499 := by exact prefixLift 1735499
  have htrace : WordTrace (prefixWord ++ tailWord_1735499) baseStart_1735499 baseEnd_1735499 := by
    simpa [prefixWord, tailWord_1735499, baseEnd_1735499] using wordTrace_append hprefix tailTrace_1735499
  have hstable : (prefixWord ++ tailWord_1735499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735499).length < 2 ^ (prefixWord ++ tailWord_1735499).sum := by decide
  have hdescent : baseEnd_1735499 < baseStart_1735499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735563 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 5, 2]
def baseStart_1735563 : Nat := 118140960795 + 1735563 * 2 ^ 59
def prefixEnd_1735563 : Nat := 4983230072969 + 3 ^ 40 * 1735563 * 2
def baseEnd_1735563 : Nat := 891178025159298335480797

theorem tailTrace_1735563 : CollatzResearch.WordTrace tailWord_1735563 prefixEnd_1735563 891178025159298335480797 := by
  unfold tailWord_1735563
  simp only [CollatzResearch.WordTrace]
  refine ⟨63301183011359136407059343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42200788674239424271372895 63301183011359136407059343)
  ·
    refine ⟨94951774517038704610589015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63301183011359136407059343 94951774517038704610589015)
    ·
      refine ⟨142427661775558056915883523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94951774517038704610589015 142427661775558056915883523)
      ·
        refine ⟨213641492663337085373825285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142427661775558056915883523 213641492663337085373825285)
        ·
          refine ⟨40057779874375703507592241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213641492663337085373825285 40057779874375703507592241)
          ·
            refine ⟨30043334905781777630694181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40057779874375703507592241 30043334905781777630694181)
            ·
              refine ⟨5633125294834083305755159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30043334905781777630694181 5633125294834083305755159)
              ·
                refine ⟨8449687942251124958632739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633125294834083305755159 8449687942251124958632739)
                ·
                  refine ⟨12674531913376687437949109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449687942251124958632739 12674531913376687437949109)
                  ·
                    refine ⟨1188237366879064447307729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12674531913376687437949109 1188237366879064447307729)
                    ·
                      refine ⟨891178025159298335480797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188237366879064447307729 891178025159298335480797)
                      ·
                        rfl

theorem cell23_1735563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5, 2].length) (baseStart_1735563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735563 prefixEnd_1735563 := by exact prefixLift 1735563
  have htrace : WordTrace (prefixWord ++ tailWord_1735563) baseStart_1735563 baseEnd_1735563 := by
    simpa [prefixWord, tailWord_1735563, baseEnd_1735563] using wordTrace_append hprefix tailTrace_1735563
  have hstable : (prefixWord ++ tailWord_1735563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735563).length < 2 ^ (prefixWord ++ tailWord_1735563).sum := by decide
  have hdescent : baseEnd_1735563 < baseStart_1735563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735573 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1735573 : Nat := 118140960795 + 1735573 * 2 ^ 59
def prefixEnd_1735573 : Nat := 4983230072969 + 3 ^ 40 * 1735573 * 2
def baseEnd_1735573 : Nat := 297061053321947765451917

theorem tailTrace_1735573 : CollatzResearch.WordTrace tailWord_1735573 prefixEnd_1735573 297061053321947765451917 := by
  unfold tailWord_1735573
  simp only [CollatzResearch.WordTrace]
  refine ⟨63301547741322908114923373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42201031827548605409948915 63301547741322908114923373)
  ·
    refine ⟨23738080402996090543096265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63301547741322908114923373 23738080402996090543096265)
    ·
      refine ⟨17803560302247067907322199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23738080402996090543096265 17803560302247067907322199)
      ·
        refine ⟨26705340453370601860983299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17803560302247067907322199 26705340453370601860983299)
        ·
          refine ⟨40058010680055902791474949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26705340453370601860983299 40058010680055902791474949)
          ·
            refine ⟨7510877002510481773401553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40058010680055902791474949 7510877002510481773401553)
            ·
              refine ⟨5633157751882861330051165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7510877002510481773401553 5633157751882861330051165)
              ·
                refine ⟨2112434156956072998769187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5633157751882861330051165 2112434156956072998769187)
                ·
                  refine ⟨3168651235434109498153781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112434156956072998769187 3168651235434109498153781)
                  ·
                    refine ⟨297061053321947765451917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3168651235434109498153781 297061053321947765451917)
                    ·
                      rfl

theorem cell23_1735573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1735573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735573 prefixEnd_1735573 := by exact prefixLift 1735573
  have htrace : WordTrace (prefixWord ++ tailWord_1735573) baseStart_1735573 baseEnd_1735573 := by
    simpa [prefixWord, tailWord_1735573, baseEnd_1735573] using wordTrace_append hprefix tailTrace_1735573
  have hstable : (prefixWord ++ tailWord_1735573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735573).length < 2 ^ (prefixWord ++ tailWord_1735573).sum := by decide
  have hdescent : baseEnd_1735573 < baseStart_1735573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735574 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1735574 : Nat := 118140960795 + 1735574 * 2 ^ 59
def prefixEnd_1735574 : Nat := 4983230072969 + 3 ^ 40 * 1735574 * 2
def baseEnd_1735574 : Nat := 891183673446497792443247

theorem tailTrace_1735574 : CollatzResearch.WordTrace tailWord_1735574 prefixEnd_1735574 891183673446497792443247 := by
  unfold tailWord_1735574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956349013394955330356861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42201056142879523523806517 3956349013394955330356861)
  ·
    refine ⟨1483630880023108248883823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3956349013394955330356861 1483630880023108248883823)
    ·
      refine ⟨2225446320034662373325735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483630880023108248883823 2225446320034662373325735)
      ·
        refine ⟨3338169480051993559988603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225446320034662373325735 3338169480051993559988603)
        ·
          refine ⟨5007254220077990339982905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338169480051993559988603 5007254220077990339982905)
          ·
            refine ⟨3755440665058492754987179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007254220077990339982905 3755440665058492754987179)
            ·
              refine ⟨5633160997587739132480769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755440665058492754987179 5633160997587739132480769)
              ·
                refine ⟨4224870748190804349360577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633160997587739132480769 4224870748190804349360577)
                ·
                  refine ⟨3168653061143103262020433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224870748190804349360577 3168653061143103262020433)
                  ·
                    refine ⟨2376489795857327446515325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168653061143103262020433 2376489795857327446515325)
                    ·
                      refine ⟨891183673446497792443247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376489795857327446515325 891183673446497792443247)
                      ·
                        rfl

theorem cell23_1735574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1735574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735574 prefixEnd_1735574 := by exact prefixLift 1735574
  have htrace : WordTrace (prefixWord ++ tailWord_1735574) baseStart_1735574 baseEnd_1735574 := by
    simpa [prefixWord, tailWord_1735574, baseEnd_1735574] using wordTrace_append hprefix tailTrace_1735574
  have hstable : (prefixWord ++ tailWord_1735574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735574).length < 2 ^ (prefixWord ++ tailWord_1735574).sum := by decide
  have hdescent : baseEnd_1735574 < baseStart_1735574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735610 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_1735610 : Nat := 118140960795 + 1735610 * 2 ^ 59
def prefixEnd_1735610 : Nat := 4983230072969 + 3 ^ 40 * 1735610 * 2
def baseEnd_1735610 : Nat := 891202158750059651593081

theorem tailTrace_1735610 : CollatzResearch.WordTrace tailWord_1735610 prefixEnd_1735610 891202158750059651593081 := by
  unfold tailWord_1735610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825724310547215858505071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42201931494792575622680189 15825724310547215858505071)
  ·
    refine ⟨23738586465820823787757607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825724310547215858505071 23738586465820823787757607)
    ·
      refine ⟨35607879698731235681636411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23738586465820823787757607 35607879698731235681636411)
      ·
        refine ⟨53411819548096853522454617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35607879698731235681636411 53411819548096853522454617)
        ·
          refine ⟨40058864661072640141840963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53411819548096853522454617 40058864661072640141840963)
          ·
            refine ⟨60088296991608960212761445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40058864661072640141840963 60088296991608960212761445)
            ·
              refine ⟨11266555685926680039892771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60088296991608960212761445 11266555685926680039892771)
              ·
                refine ⟨16899833528890020059839157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11266555685926680039892771 16899833528890020059839157)
                ·
                  refine ⟨1584359393333439380609921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16899833528890020059839157 1584359393333439380609921)
                  ·
                    refine ⟨1188269545000079535457441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584359393333439380609921 1188269545000079535457441)
                    ·
                      refine ⟨891202158750059651593081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188269545000079535457441 891202158750059651593081)
                      ·
                        rfl

theorem cell23_1735610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_1735610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735610 prefixEnd_1735610 := by exact prefixLift 1735610
  have htrace : WordTrace (prefixWord ++ tailWord_1735610) baseStart_1735610 baseEnd_1735610 := by
    simpa [prefixWord, tailWord_1735610, baseEnd_1735610] using wordTrace_append hprefix tailTrace_1735610
  have hstable : (prefixWord ++ tailWord_1735610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735610).length < 2 ^ (prefixWord ++ tailWord_1735610).sum := by decide
  have hdescent : baseEnd_1735610 < baseStart_1735610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735616 : List Nat := [2, 1, 1, 2, 3, 3, 2, 9]
def baseStart_1735616 : Nat := 118140960795 + 1735616 * 2 ^ 59
def prefixEnd_1735616 : Nat := 4983230072969 + 3 ^ 40 * 1735616 * 2
def baseEnd_1735616 : Nat := 33007601467925430671039

theorem tailTrace_1735616 : CollatzResearch.WordTrace tailWord_1735616 prefixEnd_1735616 33007601467925430671039 := by
  unfold tailWord_1735616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31651558040083563229369351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42202077386778084305825801 31651558040083563229369351)
  ·
    refine ⟨47477337060125344844054027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31651558040083563229369351 47477337060125344844054027)
    ·
      refine ⟨71216005590188017266081041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47477337060125344844054027 71216005590188017266081041)
      ·
        refine ⟨53412004192641012949560781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71216005590188017266081041 53412004192641012949560781)
        ·
          refine ⟨20029501572240379856085293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53412004192641012949560781 20029501572240379856085293)
          ·
            refine ⟨7511063089590142446031985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20029501572240379856085293 7511063089590142446031985)
            ·
              refine ⟨5633297317192606834523989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7511063089590142446031985 5633297317192606834523989)
              ·
                refine ⟨33007601467925430671039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5633297317192606834523989 33007601467925430671039)
                ·
                  rfl

theorem cell23_1735616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_1735616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735616 prefixEnd_1735616 := by exact prefixLift 1735616
  have htrace : WordTrace (prefixWord ++ tailWord_1735616) baseStart_1735616 baseEnd_1735616 := by
    simpa [prefixWord, tailWord_1735616, baseEnd_1735616] using wordTrace_append hprefix tailTrace_1735616
  have hstable : (prefixWord ++ tailWord_1735616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735616).length < 2 ^ (prefixWord ++ tailWord_1735616).sum := by decide
  have hdescent : baseEnd_1735616 < baseStart_1735616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735630 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1735630 : Nat := 118140960795 + 1735630 * 2 ^ 59
def prefixEnd_1735630 : Nat := 4983230072969 + 3 ^ 40 * 1735630 * 2
def baseEnd_1735630 : Nat := 891212428363149573342989

theorem tailTrace_1735630 : CollatzResearch.WordTrace tailWord_1735630 prefixEnd_1735630 891212428363149573342989 := by
  unfold tailWord_1735630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912953337764550856218543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42202417801410937899832229 7912953337764550856218543)
  ·
    refine ⟨11869430006646826284327815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7912953337764550856218543 11869430006646826284327815)
    ·
      refine ⟨17804145009970239426491723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869430006646826284327815 17804145009970239426491723)
      ·
        refine ⟨26706217514955359139737585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804145009970239426491723 26706217514955359139737585)
        ·
          refine ⟨20029663136216519354803189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26706217514955359139737585 20029663136216519354803189)
          ·
            refine ⟨1877780919020298689512799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20029663136216519354803189 1877780919020298689512799)
            ·
              refine ⟨2816671378530448034269199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877780919020298689512799 2816671378530448034269199)
              ·
                refine ⟨4225007067795672051403799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816671378530448034269199 4225007067795672051403799)
                ·
                  refine ⟨6337510601693508077105699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225007067795672051403799 6337510601693508077105699)
                  ·
                    refine ⟨9506265902540262115658549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6337510601693508077105699 9506265902540262115658549)
                    ·
                      refine ⟨891212428363149573342989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9506265902540262115658549 891212428363149573342989)
                      ·
                        rfl

theorem cell23_1735630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1735630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735630 prefixEnd_1735630 := by exact prefixLift 1735630
  have htrace : WordTrace (prefixWord ++ tailWord_1735630) baseStart_1735630 baseEnd_1735630 := by
    simpa [prefixWord, tailWord_1735630, baseEnd_1735630] using wordTrace_append hprefix tailTrace_1735630
  have hstable : (prefixWord ++ tailWord_1735630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735630).length < 2 ^ (prefixWord ++ tailWord_1735630).sum := by decide
  have hdescent : baseEnd_1735630 < baseStart_1735630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735637 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1735637 : Nat := 118140960795 + 1735637 * 2 ^ 59
def prefixEnd_1735637 : Nat := 4983230072969 + 3 ^ 40 * 1735637 * 2
def baseEnd_1735637 : Nat := 297072007575910348651819

theorem tailTrace_1735637 : CollatzResearch.WordTrace tailWord_1735637 prefixEnd_1735637 297072007575910348651819 := by
  unfold tailWord_1735637
  simp only [CollatzResearch.WordTrace]
  refine ⟨63303882013091047045253165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42202588008727364696835443 63303882013091047045253165)
  ·
    refine ⟨23738955754909142641969937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63303882013091047045253165 23738955754909142641969937)
    ·
      refine ⟨17804216816181856981477453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23738955754909142641969937 17804216816181856981477453)
      ·
        refine ⟨6676581306068196368054045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17804216816181856981477453 6676581306068196368054045)
        ·
          refine ⟨2503717989775573638020267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6676581306068196368054045 2503717989775573638020267)
          ·
            refine ⟨3755576984663360457030401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503717989775573638020267 3755576984663360457030401)
            ·
              refine ⟨2816682738497520342772801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755576984663360457030401 2816682738497520342772801)
              ·
                refine ⟨2112512053873140257079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2816682738497520342772801 2112512053873140257079601)
                ·
                  refine ⟨1584384040404855192809701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112512053873140257079601 1584384040404855192809701)
                  ·
                    refine ⟨297072007575910348651819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584384040404855192809701 297072007575910348651819)
                    ·
                      rfl

theorem cell23_1735637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1735637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735637 prefixEnd_1735637 := by exact prefixLift 1735637
  have htrace : WordTrace (prefixWord ++ tailWord_1735637) baseStart_1735637 baseEnd_1735637 := by
    simpa [prefixWord, tailWord_1735637, baseEnd_1735637] using wordTrace_append hprefix tailTrace_1735637
  have hstable : (prefixWord ++ tailWord_1735637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735637).length < 2 ^ (prefixWord ++ tailWord_1735637).sum := by decide
  have hdescent : baseEnd_1735637 < baseStart_1735637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735638 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1735638 : Nat := 118140960795 + 1735638 * 2 ^ 59
def prefixEnd_1735638 : Nat := 4983230072969 + 3 ^ 40 * 1735638 * 2
def baseEnd_1735638 : Nat := 891216536208385542042953

theorem tailTrace_1735638 : CollatzResearch.WordTrace tailWord_1735638 prefixEnd_1735638 891216536208385542042953 := by
  unfold tailWord_1735638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956494905380464013502473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42202612324058282810693045 3956494905380464013502473)
  ·
    refine ⟨2967371179035348010126855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3956494905380464013502473 2967371179035348010126855)
    ·
      refine ⟨4451056768553022015190283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967371179035348010126855 4451056768553022015190283)
      ·
        refine ⟨6676585152829533022785425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451056768553022015190283 6676585152829533022785425)
        ·
          refine ⟨5007438864622149767089069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676585152829533022785425 5007438864622149767089069)
          ·
            refine ⟨1877789574233306162658401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5007438864622149767089069 1877789574233306162658401)
            ·
              refine ⟨1408342180674979621993801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877789574233306162658401 1408342180674979621993801)
              ·
                refine ⟨1056256635506234716495351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408342180674979621993801 1056256635506234716495351)
                ·
                  refine ⟨1584384953259352074743027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056256635506234716495351 1584384953259352074743027)
                  ·
                    refine ⟨2376577429889028112114541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584384953259352074743027 2376577429889028112114541)
                    ·
                      refine ⟨891216536208385542042953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376577429889028112114541 891216536208385542042953)
                      ·
                        rfl

theorem cell23_1735638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1735638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735638 prefixEnd_1735638 := by exact prefixLift 1735638
  have htrace : WordTrace (prefixWord ++ tailWord_1735638) baseStart_1735638 baseEnd_1735638 := by
    simpa [prefixWord, tailWord_1735638, baseEnd_1735638] using wordTrace_append hprefix tailTrace_1735638
  have hstable : (prefixWord ++ tailWord_1735638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735638).length < 2 ^ (prefixWord ++ tailWord_1735638).sum := by decide
  have hdescent : baseEnd_1735638 < baseStart_1735638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735650 : List Nat := [3, 3, 3, 1, 1, 1, 3, 8]
def baseStart_1735650 : Nat := 118140960795 + 1735650 * 2 ^ 59
def prefixEnd_1735650 : Nat := 4983230072969 + 3 ^ 40 * 1735650 * 2
def baseEnd_1735650 : Nat := 33008248073194055373811

theorem tailTrace_1735650 : CollatzResearch.WordTrace tailWord_1735650 prefixEnd_1735650 33008248073194055373811 := by
  unfold tailWord_1735650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826089040510987566369101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42202904108029300176984269 15826089040510987566369101)
  ·
    refine ⟨5934783390191620337388413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15826089040510987566369101 5934783390191620337388413)
    ·
      refine ⟨2225543771321857626520655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5934783390191620337388413 2225543771321857626520655)
      ·
        refine ⟨3338315656982786439780983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225543771321857626520655 3338315656982786439780983)
        ·
          refine ⟨5007473485474179659671475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338315656982786439780983 5007473485474179659671475)
          ·
            refine ⟨7511210228211269489507213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007473485474179659671475 7511210228211269489507213)
            ·
              refine ⟨2816703835579226058565205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7511210228211269489507213 2816703835579226058565205)
              ·
                refine ⟨33008248073194055373811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2816703835579226058565205 33008248073194055373811)
                ·
                  rfl

theorem cell23_1735650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_1735650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735650 prefixEnd_1735650 := by exact prefixLift 1735650
  have htrace : WordTrace (prefixWord ++ tailWord_1735650) baseStart_1735650 baseEnd_1735650 := by
    simpa [prefixWord, tailWord_1735650, baseEnd_1735650] using wordTrace_append hprefix tailTrace_1735650
  have hstable : (prefixWord ++ tailWord_1735650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735650).length < 2 ^ (prefixWord ++ tailWord_1735650).sum := by decide
  have hdescent : baseEnd_1735650 < baseStart_1735650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735678 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1735678 : Nat := 118140960795 + 1735678 * 2 ^ 59
def prefixEnd_1735678 : Nat := 4983230072969 + 3 ^ 40 * 1735678 * 2
def baseEnd_1735678 : Nat := 891237075434565385542769

theorem tailTrace_1735678 : CollatzResearch.WordTrace tailWord_1735678 prefixEnd_1735678 891237075434565385542769 := by
  unfold tailWord_1735678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913172175742813880936961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42203584937295007364997125 7913172175742813880936961)
  ·
    refine ⟨5934879131807110410702721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913172175742813880936961 5934879131807110410702721)
    ·
      refine ⟨4451159348855332808027041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5934879131807110410702721 4451159348855332808027041)
      ·
        refine ⟨3338369511641499606020281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4451159348855332808027041 3338369511641499606020281)
        ·
          refine ⟨2503777133731124704515211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338369511641499606020281 2503777133731124704515211)
          ·
            refine ⟨3755665700596687056772817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503777133731124704515211 3755665700596687056772817)
            ·
              refine ⟨2816749275447515292579613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755665700596687056772817 2816749275447515292579613)
              ·
                refine ⟨1056280978292818234717355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2816749275447515292579613 1056280978292818234717355)
                ·
                  refine ⟨1584421467439227352076033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056280978292818234717355 1584421467439227352076033)
                  ·
                    refine ⟨1188316100579420514057025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584421467439227352076033 1188316100579420514057025)
                    ·
                      refine ⟨891237075434565385542769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188316100579420514057025 891237075434565385542769)
                      ·
                        rfl

theorem cell23_1735678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1735678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735678 prefixEnd_1735678 := by exact prefixLift 1735678
  have htrace : WordTrace (prefixWord ++ tailWord_1735678) baseStart_1735678 baseEnd_1735678 := by
    simpa [prefixWord, tailWord_1735678, baseEnd_1735678] using wordTrace_append hprefix tailTrace_1735678
  have hstable : (prefixWord ++ tailWord_1735678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735678).length < 2 ^ (prefixWord ++ tailWord_1735678).sum := by decide
  have hdescent : baseEnd_1735678 < baseStart_1735678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735687 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1735687 : Nat := 118140960795 + 1735687 * 2 ^ 59
def prefixEnd_1735687 : Nat := 4983230072969 + 3 ^ 40 * 1735687 * 2
def baseEnd_1735687 : Nat := 891241696760455850330227

theorem tailTrace_1735687 : CollatzResearch.WordTrace tailWord_1735687 prefixEnd_1735687 891241696760455850330227 := by
  unfold tailWord_1735687
  simp only [CollatzResearch.WordTrace]
  refine ⟨63305705662909905584573315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42203803775273270389715543 63305705662909905584573315)
  ·
    refine ⟨94958558494364858376859973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63305705662909905584573315 94958558494364858376859973)
    ·
      refine ⟨17804729717693410945661245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94958558494364858376859973 17804729717693410945661245)
      ·
        refine ⟨6676773644135029104622967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17804729717693410945661245 6676773644135029104622967)
        ·
          refine ⟨10015160466202543656934451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676773644135029104622967 10015160466202543656934451)
          ·
            refine ⟨15022740699303815485401677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10015160466202543656934451 15022740699303815485401677)
            ·
              refine ⟨5633527762238930807025629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15022740699303815485401677 5633527762238930807025629)
              ·
                refine ⟨2112572910839599052634611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5633527762238930807025629 2112572910839599052634611)
                ·
                  refine ⟨3168859366259398578951917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112572910839599052634611 3168859366259398578951917)
                  ·
                    refine ⟨1188322262347274467106969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168859366259398578951917 1188322262347274467106969)
                    ·
                      refine ⟨891241696760455850330227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188322262347274467106969 891241696760455850330227)
                      ·
                        rfl

theorem cell23_1735687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1735687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735687 prefixEnd_1735687 := by exact prefixLift 1735687
  have htrace : WordTrace (prefixWord ++ tailWord_1735687) baseStart_1735687 baseEnd_1735687 := by
    simpa [prefixWord, tailWord_1735687, baseEnd_1735687] using wordTrace_append hprefix tailTrace_1735687
  have hstable : (prefixWord ++ tailWord_1735687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735687).length < 2 ^ (prefixWord ++ tailWord_1735687).sum := by decide
  have hdescent : baseEnd_1735687 < baseStart_1735687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735694 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1735694 : Nat := 118140960795 + 1735694 * 2 ^ 59
def prefixEnd_1735694 : Nat := 4983230072969 + 3 ^ 40 * 1735694 * 2
def baseEnd_1735694 : Nat := 891245291125037322942695

theorem tailTrace_1735694 : CollatzResearch.WordTrace tailWord_1735694 prefixEnd_1735694 891245291125037322942695 := by
  unfold tailWord_1735694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913245121735568222509767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42203973982589697186718757 7913245121735568222509767)
  ·
    refine ⟨11869867682603352333764651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7913245121735568222509767 11869867682603352333764651)
    ·
      refine ⟨17804801523905028500646977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869867682603352333764651 17804801523905028500646977)
      ·
        refine ⟨13353601142928771375485233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804801523905028500646977 13353601142928771375485233)
        ·
          refine ⟨10015200857196578531613925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13353601142928771375485233 10015200857196578531613925)
          ·
            refine ⟨1877850160724358474677611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10015200857196578531613925 1877850160724358474677611)
            ·
              refine ⟨2816775241086537712016417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877850160724358474677611 2816775241086537712016417)
              ·
                refine ⟨2112581430814903284012313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2816775241086537712016417 2112581430814903284012313)
                ·
                  refine ⟨1584436073111177463009235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112581430814903284012313 1584436073111177463009235)
                  ·
                    refine ⟨2376654109666766194513853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584436073111177463009235 2376654109666766194513853)
                    ·
                      refine ⟨891245291125037322942695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376654109666766194513853 891245291125037322942695)
                      ·
                        rfl

theorem cell23_1735694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1735694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735694 prefixEnd_1735694 := by exact prefixLift 1735694
  have htrace : WordTrace (prefixWord ++ tailWord_1735694) baseStart_1735694 baseEnd_1735694 := by
    simpa [prefixWord, tailWord_1735694, baseEnd_1735694] using wordTrace_append hprefix tailTrace_1735694
  have hstable : (prefixWord ++ tailWord_1735694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735694).length < 2 ^ (prefixWord ++ tailWord_1735694).sum := by decide
  have hdescent : baseEnd_1735694 < baseStart_1735694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735696 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1735696 : Nat := 118140960795 + 1735696 * 2 ^ 59
def prefixEnd_1735696 : Nat := 4983230072969 + 3 ^ 40 * 1735696 * 2
def baseEnd_1735696 : Nat := 891246318086346315117685

theorem tailTrace_1735696 : CollatzResearch.WordTrace tailWord_1735696 prefixEnd_1735696 891246318086346315117685 := by
  unfold tailWord_1735696
  simp only [CollatzResearch.WordTrace]
  refine ⟨31653016959938650060825471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42204022613251533414433961 31653016959938650060825471)
  ·
    refine ⟨47479525439907975091238207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31653016959938650060825471 47479525439907975091238207)
    ·
      refine ⟨71219288159861962636857311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47479525439907975091238207 71219288159861962636857311)
      ·
        refine ⟨106828932239792943955285967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71219288159861962636857311 106828932239792943955285967)
        ·
          refine ⟨160243398359689415932928951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106828932239792943955285967 160243398359689415932928951)
          ·
            refine ⟨240365097539534123899393427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160243398359689415932928951 240365097539534123899393427)
            ·
              refine ⟨360547646309301185849090141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240365097539534123899393427 360547646309301185849090141)
              ·
                refine ⟨135205367365987944693408803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360547646309301185849090141 135205367365987944693408803)
                ·
                  refine ⟨202808051048981917040113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135205367365987944693408803 202808051048981917040113205)
                  ·
                    refine ⟨19013254785842054722510613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202808051048981917040113205 19013254785842054722510613)
                    ·
                      refine ⟨891246318086346315117685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19013254785842054722510613 891246318086346315117685)
                      ·
                        rfl

theorem cell23_1735696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1735696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735696 prefixEnd_1735696 := by exact prefixLift 1735696
  have htrace : WordTrace (prefixWord ++ tailWord_1735696) baseStart_1735696 baseEnd_1735696 := by
    simpa [prefixWord, tailWord_1735696, baseEnd_1735696] using wordTrace_append hprefix tailTrace_1735696
  have hstable : (prefixWord ++ tailWord_1735696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735696).length < 2 ^ (prefixWord ++ tailWord_1735696).sum := by decide
  have hdescent : baseEnd_1735696 < baseStart_1735696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735734 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1735734 : Nat := 118140960795 + 1735734 * 2 ^ 59
def prefixEnd_1735734 : Nat := 4983230072969 + 3 ^ 40 * 1735734 * 2
def baseEnd_1735734 : Nat := 891265830351217166442511

theorem tailTrace_1735734 : CollatzResearch.WordTrace tailWord_1735734 prefixEnd_1735734 891265830351217166442511 := by
  unfold tailWord_1735734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956713743358727038220891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42204946595826421741022837 3956713743358727038220891)
  ·
    refine ⟨5935070615038090557331337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956713743358727038220891 5935070615038090557331337)
    ·
      refine ⟨4451302961278567917998503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5935070615038090557331337 4451302961278567917998503)
      ·
        refine ⟨6676954441917851876997755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451302961278567917998503 6676954441917851876997755)
        ·
          refine ⟨10015431662876777815496633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676954441917851876997755 10015431662876777815496633)
          ·
            refine ⟨7511573747157583361622475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10015431662876777815496633 7511573747157583361622475)
            ·
              refine ⟨11267360620736375042433713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511573747157583361622475 11267360620736375042433713)
              ·
                refine ⟨8450520465552281281825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11267360620736375042433713 8450520465552281281825285)
                ·
                  refine ⟨1584472587291052740342241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8450520465552281281825285 1584472587291052740342241)
                  ·
                    refine ⟨1188354440468289555256681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584472587291052740342241 1188354440468289555256681)
                    ·
                      refine ⟨891265830351217166442511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188354440468289555256681 891265830351217166442511)
                      ·
                        rfl

theorem cell23_1735734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1735734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735734 prefixEnd_1735734 := by exact prefixLift 1735734
  have htrace : WordTrace (prefixWord ++ tailWord_1735734) baseStart_1735734 baseEnd_1735734 := by
    simpa [prefixWord, tailWord_1735734, baseEnd_1735734] using wordTrace_append hprefix tailTrace_1735734
  have hstable : (prefixWord ++ tailWord_1735734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735734).length < 2 ^ (prefixWord ++ tailWord_1735734).sum := by decide
  have hdescent : baseEnd_1735734 < baseStart_1735734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735757 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1735757 : Nat := 118140960795 + 1735757 * 2 ^ 59
def prefixEnd_1735757 : Nat := 4983230072969 + 3 ^ 40 * 1735757 * 2
def baseEnd_1735757 : Nat := 99030848934030064050545

theorem tailTrace_1735757 : CollatzResearch.WordTrace tailWord_1735757 prefixEnd_1735757 99030848934030064050545 := by
  unfold tailWord_1735757
  simp only [CollatzResearch.WordTrace]
  refine ⟨63308258772656307539621525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42205505848437538359747683 63308258772656307539621525)
  ·
    refine ⟨2967574629968264415919759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63308258772656307539621525 2967574629968264415919759)
    ·
      refine ⟨4451361944952396623879639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967574629968264415919759 4451361944952396623879639)
      ·
        refine ⟨6677042917428594935819459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451361944952396623879639 6677042917428594935819459)
        ·
          refine ⟨10015564376142892403729189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677042917428594935819459 10015564376142892403729189)
          ·
            refine ⟨1877918320526792325699223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10015564376142892403729189 1877918320526792325699223)
            ·
              refine ⟨2816877480790188488548835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877918320526792325699223 2816877480790188488548835)
              ·
                refine ⟨4225316221185282732823253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816877480790188488548835 4225316221185282732823253)
                ·
                  refine ⟨99030848934030064050545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4225316221185282732823253 99030848934030064050545)
                  ·
                    rfl

theorem cell23_1735757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1735757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735757 prefixEnd_1735757 := by exact prefixLift 1735757
  have htrace : WordTrace (prefixWord ++ tailWord_1735757) baseStart_1735757 baseEnd_1735757 := by
    simpa [prefixWord, tailWord_1735757, baseEnd_1735757] using wordTrace_append hprefix tailTrace_1735757
  have hstable : (prefixWord ++ tailWord_1735757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735757).length < 2 ^ (prefixWord ++ tailWord_1735757).sum := by decide
  have hdescent : baseEnd_1735757 < baseStart_1735757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735844 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_1735844 : Nat := 118140960795 + 1735844 * 2 ^ 59
def prefixEnd_1735844 : Nat := 4983230072969 + 3 ^ 40 * 1735844 * 2
def baseEnd_1735844 : Nat := 891322313223211736067005

theorem tailTrace_1735844 : CollatzResearch.WordTrace tailWord_1735844 prefixEnd_1735844 891322313223211736067005 := by
  unfold tailWord_1735844
  simp only [CollatzResearch.WordTrace]
  refine ⟨31655715961670560699019293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42207621282227414265359057 31655715961670560699019293)
  ·
    refine ⟨11870893485626460262132235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31655715961670560699019293 11870893485626460262132235)
    ·
      refine ⟨17806340228439690393198353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11870893485626460262132235 17806340228439690393198353)
      ·
        refine ⟨13354755171329767794898765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17806340228439690393198353 13354755171329767794898765)
        ·
          refine ⟨5008033189248662923087037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13354755171329767794898765 5008033189248662923087037)
          ·
            refine ⟨1878012445968248596157639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008033189248662923087037 1878012445968248596157639)
            ·
              refine ⟨2817018668952372894236459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878012445968248596157639 2817018668952372894236459)
              ·
                refine ⟨4225528003428559341354689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817018668952372894236459 4225528003428559341354689)
                ·
                  refine ⟨3169146002571419506016017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225528003428559341354689 3169146002571419506016017)
                  ·
                    refine ⟨2376859501928564629512013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169146002571419506016017 2376859501928564629512013)
                    ·
                      refine ⟨891322313223211736067005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2376859501928564629512013 891322313223211736067005)
                      ·
                        rfl

theorem cell23_1735844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_1735844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735844 prefixEnd_1735844 := by exact prefixLift 1735844
  have htrace : WordTrace (prefixWord ++ tailWord_1735844) baseStart_1735844 baseEnd_1735844 := by
    simpa [prefixWord, tailWord_1735844, baseEnd_1735844] using wordTrace_append hprefix tailTrace_1735844
  have hstable : (prefixWord ++ tailWord_1735844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735844).length < 2 ^ (prefixWord ++ tailWord_1735844).sum := by decide
  have hdescent : baseEnd_1735844 < baseStart_1735844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735880 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1735880 : Nat := 118140960795 + 1735880 * 2 ^ 59
def prefixEnd_1735880 : Nat := 4983230072969 + 3 ^ 40 * 1735880 * 2
def baseEnd_1735880 : Nat := 891340798526773595216839

theorem tailTrace_1735880 : CollatzResearch.WordTrace tailWord_1735880 prefixEnd_1735880 891340798526773595216839 := by
  unfold tailWord_1735880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31656372475605349773174547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42208496634140466364232729 31656372475605349773174547)
  ·
    refine ⟨47484558713408024659761821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31656372475605349773174547 47484558713408024659761821)
    ·
      refine ⟨17806709517528009247410683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47484558713408024659761821 17806709517528009247410683)
      ·
        refine ⟨26710064276292013871116025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17806709517528009247410683 26710064276292013871116025)
        ·
          refine ⟨20032548207219010403337019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26710064276292013871116025 20032548207219010403337019)
          ·
            refine ⟨30048822310828515605005529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20032548207219010403337019 30048822310828515605005529)
            ·
              refine ⟨22536616733121386703754147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30048822310828515605005529 22536616733121386703754147)
              ·
                refine ⟨33804925099682080055631221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22536616733121386703754147 33804925099682080055631221)
                ·
                  refine ⟨3169211728095195005215427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33804925099682080055631221 3169211728095195005215427)
                  ·
                    refine ⟨4753817592142792507823141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3169211728095195005215427 4753817592142792507823141)
                    ·
                      refine ⟨891340798526773595216839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4753817592142792507823141 891340798526773595216839)
                      ·
                        rfl

theorem cell23_1735880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1735880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735880 prefixEnd_1735880 := by exact prefixLift 1735880
  have htrace : WordTrace (prefixWord ++ tailWord_1735880) baseStart_1735880 baseEnd_1735880 := by
    simpa [prefixWord, tailWord_1735880, baseEnd_1735880] using wordTrace_append hprefix tailTrace_1735880
  have hstable : (prefixWord ++ tailWord_1735880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735880).length < 2 ^ (prefixWord ++ tailWord_1735880).sum := by decide
  have hdescent : baseEnd_1735880 < baseStart_1735880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735917 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1735917 : Nat := 118140960795 + 1735917 * 2 ^ 59
def prefixEnd_1735917 : Nat := 4983230072969 + 3 ^ 40 * 1735917 * 2
def baseEnd_1735917 : Nat := 891359797310989950454169

theorem tailTrace_1735917 : CollatzResearch.WordTrace tailWord_1735917 prefixEnd_1735917 891359797310989950454169 := by
  unfold tailWord_1735917
  simp only [CollatzResearch.WordTrace]
  refine ⟨63314094452076654865446005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42209396301384436576964003 63314094452076654865446005)
  ·
    refine ⟨5935696354882186393635563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63314094452076654865446005 5935696354882186393635563)
    ·
      refine ⟨8903544532323279590453345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935696354882186393635563 8903544532323279590453345)
      ·
        refine ⟨6677658399242459692840009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8903544532323279590453345 6677658399242459692840009)
        ·
          refine ⟨5008243799431844769630007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6677658399242459692840009 5008243799431844769630007)
          ·
            refine ⟨7512365699147767154445011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008243799431844769630007 7512365699147767154445011)
            ·
              refine ⟨11268548548721650731667517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7512365699147767154445011 11268548548721650731667517)
              ·
                refine ⟨4225705705770619024375319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11268548548721650731667517 4225705705770619024375319)
                ·
                  refine ⟨6338558558655928536562979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225705705770619024375319 6338558558655928536562979)
                  ·
                    refine ⟨9507837837983892804844469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6338558558655928536562979 9507837837983892804844469)
                    ·
                      refine ⟨891359797310989950454169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9507837837983892804844469 891359797310989950454169)
                      ·
                        rfl

theorem cell23_1735917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1735917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735917 prefixEnd_1735917 := by exact prefixLift 1735917
  have htrace : WordTrace (prefixWord ++ tailWord_1735917) baseStart_1735917 baseEnd_1735917 := by
    simpa [prefixWord, tailWord_1735917, baseEnd_1735917] using wordTrace_append hprefix tailTrace_1735917
  have hstable : (prefixWord ++ tailWord_1735917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735917).length < 2 ^ (prefixWord ++ tailWord_1735917).sum := by decide
  have hdescent : baseEnd_1735917 < baseStart_1735917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735980 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_1735980 : Nat := 118140960795 + 1735980 * 2 ^ 59
def prefixEnd_1735980 : Nat := 4983230072969 + 3 ^ 40 * 1735980 * 2
def baseEnd_1735980 : Nat := 297130715530741067988793

theorem tailTrace_1735980 : CollatzResearch.WordTrace tailWord_1735980 prefixEnd_1735980 297130715530741067988793 := by
  unfold tailWord_1735980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31658196125424208312494697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42210928167232277749992929 31658196125424208312494697)
  ·
    refine ⟨23743647094068156234371023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31658196125424208312494697 23743647094068156234371023)
    ·
      refine ⟨35615470641102234351556535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23743647094068156234371023 35615470641102234351556535)
      ·
        refine ⟨53423205961653351527334803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35615470641102234351556535 53423205961653351527334803)
        ·
          refine ⟨80134808942480027291002205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53423205961653351527334803 80134808942480027291002205)
          ·
            refine ⟨30050553353430010234125827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80134808942480027291002205 30050553353430010234125827)
            ·
              refine ⟨45075830030145015351188741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30050553353430010234125827 45075830030145015351188741)
              ·
                refine ⟨8451718130652190378347889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45075830030145015351188741 8451718130652190378347889)
                ·
                  refine ⟨6338788597989142783760917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451718130652190378347889 6338788597989142783760917)
                  ·
                    refine ⟨297130715530741067988793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6338788597989142783760917 297130715530741067988793)
                    ·
                      rfl

theorem cell23_1735980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_1735980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1735980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1735980 prefixEnd_1735980 := by exact prefixLift 1735980
  have htrace : WordTrace (prefixWord ++ tailWord_1735980) baseStart_1735980 baseEnd_1735980 := by
    simpa [prefixWord, tailWord_1735980, baseEnd_1735980] using wordTrace_append hprefix tailTrace_1735980
  have hstable : (prefixWord ++ tailWord_1735980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735980).length < 2 ^ (prefixWord ++ tailWord_1735980).sum := by decide
  have hdescent : baseEnd_1735980 < baseStart_1735980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736037 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1736037 : Nat := 118140960795 + 1736037 * 2 ^ 59
def prefixEnd_1736037 : Nat := 4983230072969 + 3 ^ 40 * 1736037 * 2
def baseEnd_1736037 : Nat := 891421414989529480953617

theorem tailTrace_1736037 : CollatzResearch.WordTrace tailWord_1736037 prefixEnd_1736037 891421414989529480953617 := by
  unfold tailWord_1736037
  simp only [CollatzResearch.WordTrace]
  refine ⟨63318471211641915359814365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42212314141094610239876243 63318471211641915359814365)
  ·
    refine ⟨23744426704365718259930387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63318471211641915359814365 23744426704365718259930387)
    ·
      refine ⟨35616640056548577389895581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23744426704365718259930387 35616640056548577389895581)
      ·
        refine ⟨13356240021205716521210843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35616640056548577389895581 13356240021205716521210843)
        ·
          refine ⟨20034360031808574781816265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13356240021205716521210843 20034360031808574781816265)
          ·
            refine ⟨15025770023856431086362199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20034360031808574781816265 15025770023856431086362199)
            ·
              refine ⟨22538655035784646629543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15025770023856431086362199 22538655035784646629543299)
              ·
                refine ⟨33807982553676969944314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22538655035784646629543299 33807982553676969944314949)
                ·
                  refine ⟨6338996728814431864559053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33807982553676969944314949 6338996728814431864559053)
                  ·
                    refine ⟨2377123773305411949209645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338996728814431864559053 2377123773305411949209645)
                    ·
                      refine ⟨891421414989529480953617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377123773305411949209645 891421414989529480953617)
                      ·
                        rfl

theorem cell23_1736037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1736037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736037 prefixEnd_1736037 := by exact prefixLift 1736037
  have htrace : WordTrace (prefixWord ++ tailWord_1736037) baseStart_1736037 baseEnd_1736037 := by
    simpa [prefixWord, tailWord_1736037, baseEnd_1736037] using wordTrace_append hprefix tailTrace_1736037
  have hstable : (prefixWord ++ tailWord_1736037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736037).length < 2 ^ (prefixWord ++ tailWord_1736037).sum := by decide
  have hdescent : baseEnd_1736037 < baseStart_1736037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736044 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 5]
def baseStart_1736044 : Nat := 118140960795 + 1736044 * 2 ^ 59
def prefixEnd_1736044 : Nat := 4983230072969 + 3 ^ 40 * 1736044 * 2
def baseEnd_1736044 : Nat := 99047223261567883729565

theorem tailTrace_1736044 : CollatzResearch.WordTrace tailWord_1736044 prefixEnd_1736044 99047223261567883729565 := by
  unfold tailWord_1736044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31659363261308277777659593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42212484348411037036879457 31659363261308277777659593)
  ·
    refine ⟨23744522445981208333244695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31659363261308277777659593 23744522445981208333244695)
    ·
      refine ⟨35616783668971812499867043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23744522445981208333244695 35616783668971812499867043)
      ·
        refine ⟨53425175503457718749800565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35616783668971812499867043 53425175503457718749800565)
        ·
          refine ⟨5008610203449161132793803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53425175503457718749800565 5008610203449161132793803)
          ·
            refine ⟨7512915305173741699190705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008610203449161132793803 7512915305173741699190705)
            ·
              refine ⟨5634686478880306274393029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7512915305173741699190705 5634686478880306274393029)
              ·
                refine ⟨1056503714790057426448693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5634686478880306274393029 1056503714790057426448693)
                ·
                  refine ⟨99047223261567883729565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056503714790057426448693 99047223261567883729565)
                  ·
                    rfl

theorem cell23_1736044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_1736044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736044 prefixEnd_1736044 := by exact prefixLift 1736044
  have htrace : WordTrace (prefixWord ++ tailWord_1736044) baseStart_1736044 baseEnd_1736044 := by
    simpa [prefixWord, tailWord_1736044, baseEnd_1736044] using wordTrace_append hprefix tailTrace_1736044
  have hstable : (prefixWord ++ tailWord_1736044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736044).length < 2 ^ (prefixWord ++ tailWord_1736044).sum := by decide
  have hdescent : baseEnd_1736044 < baseStart_1736044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736078 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_1736078 : Nat := 118140960795 + 1736078 * 2 ^ 59
def prefixEnd_1736078 : Nat := 4983230072969 + 3 ^ 40 * 1736078 * 2
def baseEnd_1736078 : Nat := 99049163077373757837881

theorem tailTrace_1736078 : CollatzResearch.WordTrace tailWord_1736078 prefixEnd_1736078 99049163077373757837881 := by
  unfold tailWord_1736078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7914995825561672420257111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42213311069662252908037925 7914995825561672420257111)
  ·
    refine ⟨11872493738342508630385667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7914995825561672420257111 11872493738342508630385667)
    ·
      refine ⟨17808740607513762945578501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11872493738342508630385667 17808740607513762945578501)
      ·
        refine ⟨3339138863908830552295969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17808740607513762945578501 3339138863908830552295969)
        ·
          refine ⟨2504354147931622914221977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339138863908830552295969 2504354147931622914221977)
          ·
            refine ⟨1878265610948717185666483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504354147931622914221977 1878265610948717185666483)
            ·
              refine ⟨2817398416423075778499725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878265610948717185666483 2817398416423075778499725)
              ·
                refine ⟨1056524406158653416937397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817398416423075778499725 1056524406158653416937397)
                ·
                  refine ⟨99049163077373757837881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056524406158653416937397 99049163077373757837881)
                  ·
                    rfl

theorem cell23_1736078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_1736078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736078 prefixEnd_1736078 := by exact prefixLift 1736078
  have htrace : WordTrace (prefixWord ++ tailWord_1736078) baseStart_1736078 baseEnd_1736078 := by
    simpa [prefixWord, tailWord_1736078, baseEnd_1736078] using wordTrace_append hprefix tailTrace_1736078
  have hstable : (prefixWord ++ tailWord_1736078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736078).length < 2 ^ (prefixWord ++ tailWord_1736078).sum := by decide
  have hdescent : baseEnd_1736078 < baseStart_1736078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736080 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1736080 : Nat := 118140960795 + 1736080 * 2 ^ 59
def prefixEnd_1736080 : Nat := 4983230072969 + 3 ^ 40 * 1736080 * 2
def baseEnd_1736080 : Nat := 891443494657672812715919

theorem tailTrace_1736080 : CollatzResearch.WordTrace tailWord_1736080 prefixEnd_1736080 891443494657672812715919 := by
  unfold tailWord_1736080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31660019775243066851814847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42213359700324089135753129 31660019775243066851814847)
  ·
    refine ⟨47490029662864600277722271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31660019775243066851814847 47490029662864600277722271)
    ·
      refine ⟨71235044494296900416583407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47490029662864600277722271 71235044494296900416583407)
      ·
        refine ⟨106852566741445350624875111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71235044494296900416583407 106852566741445350624875111)
        ·
          refine ⟨160278850112168025937312667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106852566741445350624875111 160278850112168025937312667)
          ·
            refine ⟨240418275168252038905969001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160278850112168025937312667 240418275168252038905969001)
            ·
              refine ⟨180313706376189029179476751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240418275168252038905969001 180313706376189029179476751)
              ·
                refine ⟨270470559564283543769215127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180313706376189029179476751 270470559564283543769215127)
                ·
                  refine ⟨405705839346425315653822691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270470559564283543769215127 405705839346425315653822691)
                  ·
                    refine ⟨608558759019637973480734037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 405705839346425315653822691 608558759019637973480734037)
                    ·
                      refine ⟨891443494657672812715919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 608558759019637973480734037 891443494657672812715919)
                      ·
                        rfl

theorem cell23_1736080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1736080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736080 prefixEnd_1736080 := by exact prefixLift 1736080
  have htrace : WordTrace (prefixWord ++ tailWord_1736080) baseStart_1736080 baseEnd_1736080 := by
    simpa [prefixWord, tailWord_1736080, baseEnd_1736080] using wordTrace_append hprefix tailTrace_1736080
  have hstable : (prefixWord ++ tailWord_1736080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736080).length < 2 ^ (prefixWord ++ tailWord_1736080).sum := by decide
  have hdescent : baseEnd_1736080 < baseStart_1736080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736127 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1736127 : Nat := 118140960795 + 1736127 * 2 ^ 59
def prefixEnd_1736127 : Nat := 4983230072969 + 3 ^ 40 * 1736127 * 2
def baseEnd_1736127 : Nat := 891467628248434128828203

theorem tailTrace_1736127 : CollatzResearch.WordTrace tailWord_1736127 prefixEnd_1736127 891467628248434128828203 := by
  unfold tailWord_1736127
  simp only [CollatzResearch.WordTrace]
  refine ⟨63321753781315860730590635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42214502520877240487060423 63321753781315860730590635)
  ·
    refine ⟨94982630671973791095885953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63321753781315860730590635 94982630671973791095885953)
    ·
      refine ⟨71236973003980343321914465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94982630671973791095885953 71236973003980343321914465)
      ·
        refine ⟨53427729752985257491435849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71236973003980343321914465 53427729752985257491435849)
        ·
          refine ⟨40070797314738943118576887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53427729752985257491435849 40070797314738943118576887)
          ·
            refine ⟨60106195972108414677865331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40070797314738943118576887 60106195972108414677865331)
            ·
              refine ⟨90159293958162622016797997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60106195972108414677865331 90159293958162622016797997)
              ·
                refine ⟨33809735234310983256299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90159293958162622016797997 33809735234310983256299249)
                ·
                  refine ⟨25357301425733237442224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33809735234310983256299249 25357301425733237442224437)
                  ·
                    refine ⟨2377247008662491010208541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25357301425733237442224437 2377247008662491010208541)
                    ·
                      refine ⟨891467628248434128828203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377247008662491010208541 891467628248434128828203)
                      ·
                        rfl

theorem cell23_1736127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1736127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736127 prefixEnd_1736127 := by exact prefixLift 1736127
  have htrace : WordTrace (prefixWord ++ tailWord_1736127) baseStart_1736127 baseEnd_1736127 := by
    simpa [prefixWord, tailWord_1736127, baseEnd_1736127] using wordTrace_append hprefix tailTrace_1736127
  have hstable : (prefixWord ++ tailWord_1736127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736127).length < 2 ^ (prefixWord ++ tailWord_1736127).sum := by decide
  have hdescent : baseEnd_1736127 < baseStart_1736127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736144 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_1736144 : Nat := 118140960795 + 1736144 * 2 ^ 59
def prefixEnd_1736144 : Nat := 4983230072969 + 3 ^ 40 * 1736144 * 2
def baseEnd_1736144 : Nat := 891476357419560562315625

theorem tailTrace_1736144 : CollatzResearch.WordTrace tailWord_1736144 prefixEnd_1736144 891476357419560562315625 := by
  unfold tailWord_1736144
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661186911127136316979743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42214915881502848422639657 31661186911127136316979743)
  ·
    refine ⟨47491780366690704475469615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31661186911127136316979743 47491780366690704475469615)
    ·
      refine ⟨71237670550036056713204423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47491780366690704475469615 71237670550036056713204423)
      ·
        refine ⟨106856505825054085069806635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71237670550036056713204423 106856505825054085069806635)
        ·
          refine ⟨160284758737581127604709953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106856505825054085069806635 160284758737581127604709953)
          ·
            refine ⟨120213569053185845703532465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160284758737581127604709953 120213569053185845703532465)
            ·
              refine ⟨90160176789889384277649349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120213569053185845703532465 90160176789889384277649349)
              ·
                refine ⟨16905033148104259552059253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90160176789889384277649349 16905033148104259552059253)
                ·
                  refine ⟨1584846857634774333005555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16905033148104259552059253 1584846857634774333005555)
                  ·
                    refine ⟨2377270286452161499508333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584846857634774333005555 2377270286452161499508333)
                    ·
                      refine ⟨891476357419560562315625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377270286452161499508333 891476357419560562315625)
                      ·
                        rfl

theorem cell23_1736144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_1736144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736144 prefixEnd_1736144 := by exact prefixLift 1736144
  have htrace : WordTrace (prefixWord ++ tailWord_1736144) baseStart_1736144 baseEnd_1736144 := by
    simpa [prefixWord, tailWord_1736144, baseEnd_1736144] using wordTrace_append hprefix tailTrace_1736144
  have hstable : (prefixWord ++ tailWord_1736144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736144).length < 2 ^ (prefixWord ++ tailWord_1736144).sum := by decide
  have hdescent : baseEnd_1736144 < baseStart_1736144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736178 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1736178 : Nat := 118140960795 + 1736178 * 2 ^ 59
def prefixEnd_1736178 : Nat := 4983230072969 + 3 ^ 40 * 1736178 * 2
def baseEnd_1736178 : Nat := 891493815761813429290469

theorem tailTrace_1736178 : CollatzResearch.WordTrace tailWord_1736178 prefixEnd_1736178 891493815761813429290469 := by
  unfold tailWord_1736178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830903476032774110174297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42215742602754064293798125 15830903476032774110174297)
  ·
    refine ⟨11873177607024580582630723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15830903476032774110174297 11873177607024580582630723)
    ·
      refine ⟨17809766410536870873946085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11873177607024580582630723 17809766410536870873946085)
      ·
        refine ⟨3339331201975663288864891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17809766410536870873946085 3339331201975663288864891)
        ·
          refine ⟨5008996802963494933297337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339331201975663288864891 5008996802963494933297337)
          ·
            refine ⟨3756747602222621199973003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5008996802963494933297337 3756747602222621199973003)
            ·
              refine ⟨5635121403333931799959505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756747602222621199973003 5635121403333931799959505)
              ·
                refine ⟨4226341052500448849969629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5635121403333931799959505 4226341052500448849969629)
                ·
                  refine ⟨1584877894687668318738611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4226341052500448849969629 1584877894687668318738611)
                  ·
                    refine ⟨2377316842031502478107917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584877894687668318738611 2377316842031502478107917)
                    ·
                      refine ⟨891493815761813429290469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377316842031502478107917 891493815761813429290469)
                      ·
                        rfl

theorem cell23_1736178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1736178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736178 prefixEnd_1736178 := by exact prefixLift 1736178
  have htrace : WordTrace (prefixWord ++ tailWord_1736178) baseStart_1736178 baseEnd_1736178 := by
    simpa [prefixWord, tailWord_1736178, baseEnd_1736178] using wordTrace_append hprefix tailTrace_1736178
  have hstable : (prefixWord ++ tailWord_1736178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736178).length < 2 ^ (prefixWord ++ tailWord_1736178).sum := by decide
  have hdescent : baseEnd_1736178 < baseStart_1736178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736181 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1736181 : Nat := 118140960795 + 1736181 * 2 ^ 59
def prefixEnd_1736181 : Nat := 4983230072969 + 3 ^ 40 * 1736181 * 2
def baseEnd_1736181 : Nat := 297165118734592305850985

theorem tailTrace_1736181 : CollatzResearch.WordTrace tailWord_1736181 prefixEnd_1736181 297165118734592305850985 := by
  unfold tailWord_1736181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63323723323120227953056397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42215815548746818635370931 63323723323120227953056397)
  ·
    refine ⟨23746396246170085482396149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63323723323120227953056397 23746396246170085482396149)
    ·
      refine ⟨2226224648078445513974639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23746396246170085482396149 2226224648078445513974639)
      ·
        refine ⟨3339336972117668270961959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226224648078445513974639 3339336972117668270961959)
        ·
          refine ⟨5009005458176502406442939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339336972117668270961959 5009005458176502406442939)
          ·
            refine ⟨7513508187264753609664409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009005458176502406442939 7513508187264753609664409)
            ·
              refine ⟨5635131140448565207248307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513508187264753609664409 5635131140448565207248307)
              ·
                refine ⟨8452696710672847810872461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635131140448565207248307 8452696710672847810872461)
                ·
                  refine ⟨3169761266502317929077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8452696710672847810872461 3169761266502317929077173)
                  ·
                    refine ⟨297165118734592305850985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3169761266502317929077173 297165118734592305850985)
                    ·
                      rfl

theorem cell23_1736181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1736181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736181 prefixEnd_1736181 := by exact prefixLift 1736181
  have htrace : WordTrace (prefixWord ++ tailWord_1736181) baseStart_1736181 baseEnd_1736181 := by
    simpa [prefixWord, tailWord_1736181, baseEnd_1736181] using wordTrace_append hprefix tailTrace_1736181
  have hstable : (prefixWord ++ tailWord_1736181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736181).length < 2 ^ (prefixWord ++ tailWord_1736181).sum := by decide
  have hdescent : baseEnd_1736181 < baseStart_1736181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736184 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1736184 : Nat := 118140960795 + 1736184 * 2 ^ 59
def prefixEnd_1736184 : Nat := 4983230072969 + 3 ^ 40 * 1736184 * 2
def baseEnd_1736184 : Nat := 891496896645740405815441

theorem tailTrace_1736184 : CollatzResearch.WordTrace tailWord_1736184 prefixEnd_1736184 891496896645740405815441 := by
  unfold tailWord_1736184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661916371054679732707803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42215888494739572976943737 31661916371054679732707803)
  ·
    refine ⟨47492874556582019599061705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31661916371054679732707803 47492874556582019599061705)
    ·
      refine ⟨35619655917436514699296279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47492874556582019599061705 35619655917436514699296279)
      ·
        refine ⟨53429483876154772048944419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619655917436514699296279 53429483876154772048944419)
        ·
          refine ⟨80144225814232158073416629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53429483876154772048944419 80144225814232158073416629)
          ·
            refine ⟨7513521170084264819382809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80144225814232158073416629 7513521170084264819382809)
            ·
              refine ⟨5635140877563198614537107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513521170084264819382809 5635140877563198614537107)
              ·
                refine ⟨8452711316344797921805661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635140877563198614537107 8452711316344797921805661)
                ·
                  refine ⟨3169766743629299220677123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8452711316344797921805661 3169766743629299220677123)
                  ·
                    refine ⟨4754650115443948831015685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3169766743629299220677123 4754650115443948831015685)
                    ·
                      refine ⟨891496896645740405815441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4754650115443948831015685 891496896645740405815441)
                      ·
                        rfl

theorem cell23_1736184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1736184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736184 prefixEnd_1736184 := by exact prefixLift 1736184
  have htrace : WordTrace (prefixWord ++ tailWord_1736184) baseStart_1736184 baseEnd_1736184 := by
    simpa [prefixWord, tailWord_1736184, baseEnd_1736184] using wordTrace_append hprefix tailTrace_1736184
  have hstable : (prefixWord ++ tailWord_1736184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736184).length < 2 ^ (prefixWord ++ tailWord_1736184).sum := by decide
  have hdescent : baseEnd_1736184 < baseStart_1736184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736187 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_1736187 : Nat := 118140960795 + 1736187 * 2 ^ 59
def prefixEnd_1736187 : Nat := 4983230072969 + 3 ^ 40 * 1736187 * 2
def baseEnd_1736187 : Nat := 891498437087703894077927

theorem tailTrace_1736187 : CollatzResearch.WordTrace tailWord_1736187 prefixEnd_1736187 891498437087703894077927 := by
  unfold tailWord_1736187
  simp only [CollatzResearch.WordTrace]
  refine ⟨63323942161098490977774815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42215961440732327318516543 63323942161098490977774815)
  ·
    refine ⟨94985913241647736466662223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63323942161098490977774815 94985913241647736466662223)
    ·
      refine ⟨142478869862471604699993335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94985913241647736466662223 142478869862471604699993335)
      ·
        refine ⟨213718304793707407049990003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142478869862471604699993335 213718304793707407049990003)
        ·
          refine ⟨320577457190561110574985005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213718304793707407049990003 320577457190561110574985005)
          ·
            refine ⟨120216546446460416465619377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320577457190561110574985005 120216546446460416465619377)
            ·
              refine ⟨90162409834845312349214533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120216546446460416465619377 90162409834845312349214533)
              ·
                refine ⟨16905451844033496065477725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90162409834845312349214533 16905451844033496065477725)
                ·
                  refine ⟨6339544441512561024554147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16905451844033496065477725 6339544441512561024554147)
                  ·
                    refine ⟨9509316662268841536831221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339544441512561024554147 9509316662268841536831221)
                    ·
                      refine ⟨891498437087703894077927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9509316662268841536831221 891498437087703894077927)
                      ·
                        rfl

theorem cell23_1736187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_1736187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736187 prefixEnd_1736187 := by exact prefixLift 1736187
  have htrace : WordTrace (prefixWord ++ tailWord_1736187) baseStart_1736187 baseEnd_1736187 := by
    simpa [prefixWord, tailWord_1736187, baseEnd_1736187] using wordTrace_append hprefix tailTrace_1736187
  have hstable : (prefixWord ++ tailWord_1736187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736187).length < 2 ^ (prefixWord ++ tailWord_1736187).sum := by decide
  have hdescent : baseEnd_1736187 < baseStart_1736187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736197 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1736197 : Nat := 118140960795 + 1736197 * 2 ^ 59
def prefixEnd_1736197 : Nat := 4983230072969 + 3 ^ 40 * 1736197 * 2
def baseEnd_1736197 : Nat := 891503571894248854952881

theorem tailTrace_1736197 : CollatzResearch.WordTrace tailWord_1736197 prefixEnd_1736197 891503571894248854952881 := by
  unfold tailWord_1736197
  simp only [CollatzResearch.WordTrace]
  refine ⟨63324306891062262685638845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42216204594041508457092563 63324306891062262685638845)
  ·
    refine ⟨23746615084148348507114567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63324306891062262685638845 23746615084148348507114567)
    ·
      refine ⟨35619922626222522760671851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746615084148348507114567 35619922626222522760671851)
      ·
        refine ⟨53429883939333784141007777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619922626222522760671851 53429883939333784141007777)
        ·
          refine ⟨40072412954500338105755833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53429883939333784141007777 40072412954500338105755833)
          ·
            refine ⟨30054309715875253579316875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40072412954500338105755833 30054309715875253579316875)
            ·
              refine ⟨45081464573812880368975313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30054309715875253579316875 45081464573812880368975313)
              ·
                refine ⟨33811098430359660276731485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45081464573812880368975313 33811098430359660276731485)
                ·
                  refine ⟨12679161911384872603774307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33811098430359660276731485 12679161911384872603774307)
                  ·
                    refine ⟨19018742867077308905661461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12679161911384872603774307 19018742867077308905661461)
                    ·
                      refine ⟨891503571894248854952881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19018742867077308905661461 891503571894248854952881)
                      ·
                        rfl

theorem cell23_1736197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1736197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736197 prefixEnd_1736197 := by exact prefixLift 1736197
  have htrace : WordTrace (prefixWord ++ tailWord_1736197) baseStart_1736197 baseEnd_1736197 := by
    simpa [prefixWord, tailWord_1736197, baseEnd_1736197] using wordTrace_append hprefix tailTrace_1736197
  have hstable : (prefixWord ++ tailWord_1736197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736197).length < 2 ^ (prefixWord ++ tailWord_1736197).sum := by decide
  have hdescent : baseEnd_1736197 < baseStart_1736197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736201 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 5, 2, 2]
def baseStart_1736201 : Nat := 118140960795 + 1736201 * 2 ^ 59
def prefixEnd_1736201 : Nat := 4983230072969 + 3 ^ 40 * 1736201 * 2
def baseEnd_1736201 : Nat := 891505625816866839302863

theorem tailTrace_1736201 : CollatzResearch.WordTrace tailWord_1736201 prefixEnd_1736201 891505625816866839302863 := by
  unfold tailWord_1736201
  simp only [CollatzResearch.WordTrace]
  refine ⟨63324452783047771368784457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42216301855365180912522971 63324452783047771368784457)
  ·
    refine ⟨47493339587285828526588343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63324452783047771368784457 47493339587285828526588343)
    ·
      refine ⟨71240009380928742789882515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47493339587285828526588343 71240009380928742789882515)
      ·
        refine ⟨106860014071393114184823773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71240009380928742789882515 106860014071393114184823773)
        ·
          refine ⟨40072505276772417819308915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106860014071393114184823773 40072505276772417819308915)
          ·
            refine ⟨60108757915158626728963373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40072505276772417819308915 60108757915158626728963373)
            ·
              refine ⟨22540784218184485023361265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60108757915158626728963373 22540784218184485023361265)
              ·
                refine ⟨16905588163638363767520949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22540784218184485023361265 16905588163638363767520949)
                ·
                  refine ⟨1584898890341096603205089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16905588163638363767520949 1584898890341096603205089)
                  ·
                    refine ⟨1188674167755822452403817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584898890341096603205089 1188674167755822452403817)
                    ·
                      refine ⟨891505625816866839302863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188674167755822452403817 891505625816866839302863)
                      ·
                        rfl

theorem cell23_1736201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2, 2].length) (baseStart_1736201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736201 prefixEnd_1736201 := by exact prefixLift 1736201
  have htrace : WordTrace (prefixWord ++ tailWord_1736201) baseStart_1736201 baseEnd_1736201 := by
    simpa [prefixWord, tailWord_1736201, baseEnd_1736201] using wordTrace_append hprefix tailTrace_1736201
  have hstable : (prefixWord ++ tailWord_1736201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736201).length < 2 ^ (prefixWord ++ tailWord_1736201).sum := by decide
  have hdescent : baseEnd_1736201 < baseStart_1736201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736211 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 2, 4]
def baseStart_1736211 : Nat := 118140960795 + 1736211 * 2 ^ 59
def prefixEnd_1736211 : Nat := 4983230072969 + 3 ^ 40 * 1736211 * 2
def baseEnd_1736211 : Nat := 297170253541137266725939

theorem tailTrace_1736211 : CollatzResearch.WordTrace tailWord_1736211 prefixEnd_1736211 297170253541137266725939 := by
  unfold tailWord_1736211
  simp only [CollatzResearch.WordTrace]
  refine ⟨63324817513011543076648487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42216545008674362051098991 63324817513011543076648487)
  ·
    refine ⟨94987226269517314614972731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63324817513011543076648487 94987226269517314614972731)
    ·
      refine ⟨142480839404275971922459097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94987226269517314614972731 142480839404275971922459097)
      ·
        refine ⟨106860629553206978941844323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142480839404275971922459097 106860629553206978941844323)
        ·
          refine ⟨160290944329810468412766485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106860629553206978941844323 160290944329810468412766485)
          ·
            refine ⟨7513638015459865706848429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160290944329810468412766485 7513638015459865706848429)
            ·
              refine ⟨2817614255797449640068161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7513638015459865706848429 2817614255797449640068161)
              ·
                refine ⟨2113210691848087230051121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817614255797449640068161 2113210691848087230051121)
                ·
                  refine ⟨1584908018886065422538341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2113210691848087230051121 1584908018886065422538341)
                  ·
                    refine ⟨297170253541137266725939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584908018886065422538341 297170253541137266725939)
                    ·
                      rfl

theorem cell23_1736211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 4].length) (baseStart_1736211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736211 prefixEnd_1736211 := by exact prefixLift 1736211
  have htrace : WordTrace (prefixWord ++ tailWord_1736211) baseStart_1736211 baseEnd_1736211 := by
    simpa [prefixWord, tailWord_1736211, baseEnd_1736211] using wordTrace_append hprefix tailTrace_1736211
  have hstable : (prefixWord ++ tailWord_1736211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736211).length < 2 ^ (prefixWord ++ tailWord_1736211).sum := by decide
  have hdescent : baseEnd_1736211 < baseStart_1736211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736238 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1736238 : Nat := 118140960795 + 1736238 * 2 ^ 59
def prefixEnd_1736238 : Nat := 4983230072969 + 3 ^ 40 * 1736238 * 2
def baseEnd_1736238 : Nat := 891524624601083194540193

theorem tailTrace_1736238 : CollatzResearch.WordTrace tailWord_1736238 prefixEnd_1736238 891524624601083194540193 := by
  unfold tailWord_1736238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915725285489215835985171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42217201522609151125254245 7915725285489215835985171)
  ·
    refine ⟨11873587928233823753977757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7915725285489215835985171 11873587928233823753977757)
    ·
      refine ⟨4452595473087683907741659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11873587928233823753977757 4452595473087683907741659)
      ·
        refine ⟨6678893209631525861612489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452595473087683907741659 6678893209631525861612489)
        ·
          refine ⟨5009169907223644396209367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6678893209631525861612489 5009169907223644396209367)
          ·
            refine ⟨7513754860835466594314051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009169907223644396209367 7513754860835466594314051)
            ·
              refine ⟨11270632291253199891471077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513754860835466594314051 11270632291253199891471077)
              ·
                refine ⟨2113243554609974979650827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11270632291253199891471077 2113243554609974979650827)
                ·
                  refine ⟨3169865331914962469476241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113243554609974979650827 3169865331914962469476241)
                  ·
                    refine ⟨2377398998936221852107181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169865331914962469476241 2377398998936221852107181)
                    ·
                      refine ⟨891524624601083194540193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377398998936221852107181 891524624601083194540193)
                      ·
                        rfl

theorem cell23_1736238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1736238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736238 prefixEnd_1736238 := by exact prefixLift 1736238
  have htrace : WordTrace (prefixWord ++ tailWord_1736238) baseStart_1736238 baseEnd_1736238 := by
    simpa [prefixWord, tailWord_1736238, baseEnd_1736238] using wordTrace_append hprefix tailTrace_1736238
  have hstable : (prefixWord ++ tailWord_1736238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736238).length < 2 ^ (prefixWord ++ tailWord_1736238).sum := by decide
  have hdescent : baseEnd_1736238 < baseStart_1736238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736269 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_1736269 : Nat := 118140960795 + 1736269 * 2 ^ 59
def prefixEnd_1736269 : Nat := 4983230072969 + 3 ^ 40 * 1736269 * 2
def baseEnd_1736269 : Nat := 891540542501372573252551

theorem tailTrace_1736269 : CollatzResearch.WordTrace tailWord_1736269 prefixEnd_1736269 891540542501372573252551 := by
  unfold tailWord_1736269
  simp only [CollatzResearch.WordTrace]
  refine ⟨63326932946801418982259861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42217955297867612654839907 63326932946801418982259861)
  ·
    refine ⟨2968449981881316514793431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63326932946801418982259861 2968449981881316514793431)
    ·
      refine ⟨4452674972821974772190147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968449981881316514793431 4452674972821974772190147)
      ·
        refine ⟨6679012459232962158285221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452674972821974772190147 6679012459232962158285221)
        ·
          refine ⟨1252314836106180404678479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6679012459232962158285221 1252314836106180404678479)
          ·
            refine ⟨1878472254159270607017719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252314836106180404678479 1878472254159270607017719)
            ·
              refine ⟨2817708381238905910526579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878472254159270607017719 2817708381238905910526579)
              ·
                refine ⟨4226562571858358865789869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817708381238905910526579 4226562571858358865789869)
                ·
                  refine ⟨1584960964446884574671201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4226562571858358865789869 1584960964446884574671201)
                  ·
                    refine ⟨1188720723335163431003401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584960964446884574671201 1188720723335163431003401)
                    ·
                      refine ⟨891540542501372573252551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188720723335163431003401 891540542501372573252551)
                      ·
                        rfl

theorem cell23_1736269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_1736269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736269 prefixEnd_1736269 := by exact prefixLift 1736269
  have htrace : WordTrace (prefixWord ++ tailWord_1736269) baseStart_1736269 baseEnd_1736269 := by
    simpa [prefixWord, tailWord_1736269, baseEnd_1736269] using wordTrace_append hprefix tailTrace_1736269
  have hstable : (prefixWord ++ tailWord_1736269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736269).length < 2 ^ (prefixWord ++ tailWord_1736269).sum := by decide
  have hdescent : baseEnd_1736269 < baseStart_1736269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736325 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_1736325 : Nat := 118140960795 + 1736325 * 2 ^ 59
def prefixEnd_1736325 : Nat := 4983230072969 + 3 ^ 40 * 1736325 * 2
def baseEnd_1736325 : Nat := 891569297418024354152293

theorem tailTrace_1736325 : CollatzResearch.WordTrace tailWord_1736325 prefixEnd_1736325 891569297418024354152293 := by
  unfold tailWord_1736325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63328975434598540546298429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42219316956399027030865619 63328975434598540546298429)
  ·
    refine ⟨23748365787974452704861911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63328975434598540546298429 23748365787974452704861911)
    ·
      refine ⟨35622548681961679057292867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748365787974452704861911 35622548681961679057292867)
      ·
        refine ⟨53433823022942518585939301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35622548681961679057292867 53433823022942518585939301)
        ·
          refine ⟨10018841816801722234863619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53433823022942518585939301 10018841816801722234863619)
          ·
            refine ⟨15028262725202583352295429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018841816801722234863619 15028262725202583352295429)
            ·
              refine ⟨2817799260975484378555393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15028262725202583352295429 2817799260975484378555393)
              ·
                refine ⟨2113349445731613283916545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817799260975484378555393 2113349445731613283916545)
                ·
                  refine ⟨1585012084298709962937409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2113349445731613283916545 1585012084298709962937409)
                  ·
                    refine ⟨1188759063224032472203057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585012084298709962937409 1188759063224032472203057)
                    ·
                      refine ⟨891569297418024354152293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188759063224032472203057 891569297418024354152293)
                      ·
                        rfl

theorem cell23_1736325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_1736325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736325 prefixEnd_1736325 := by exact prefixLift 1736325
  have htrace : WordTrace (prefixWord ++ tailWord_1736325) baseStart_1736325 baseEnd_1736325 := by
    simpa [prefixWord, tailWord_1736325, baseEnd_1736325] using wordTrace_append hprefix tailTrace_1736325
  have hstable : (prefixWord ++ tailWord_1736325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736325).length < 2 ^ (prefixWord ++ tailWord_1736325).sum := by decide
  have hdescent : baseEnd_1736325 < baseStart_1736325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736331 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 5]
def baseStart_1736331 : Nat := 118140960795 + 1736331 * 2 ^ 59
def prefixEnd_1736331 : Nat := 4983230072969 + 3 ^ 40 * 1736331 * 2
def baseEnd_1736331 : Nat := 99063597589105703408585

theorem tailTrace_1736331 : CollatzResearch.WordTrace tailWord_1736331 prefixEnd_1736331 99063597589105703408585 := by
  unfold tailWord_1736331
  simp only [CollatzResearch.WordTrace]
  refine ⟨63329194272576803571016847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42219462848384535714011231 63329194272576803571016847)
  ·
    refine ⟨94993791408865205356525271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63329194272576803571016847 94993791408865205356525271)
    ·
      refine ⟨142490687113297808034787907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94993791408865205356525271 142490687113297808034787907)
      ·
        refine ⟨213736030669946712052181861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142490687113297808034787907 213736030669946712052181861)
        ·
          refine ⟨40075505750615008509784099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213736030669946712052181861 40075505750615008509784099)
          ·
            refine ⟨60113258625922512764676149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40075505750615008509784099 60113258625922512764676149)
            ·
              refine ⟨5635617996180235571688389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60113258625922512764676149 5635617996180235571688389)
              ·
                refine ⟨1056678374283794169691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5635617996180235571688389 1056678374283794169691573)
                ·
                  refine ⟨99063597589105703408585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056678374283794169691573 99063597589105703408585)
                  ·
                    rfl

theorem cell23_1736331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 5].length) (baseStart_1736331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736331 prefixEnd_1736331 := by exact prefixLift 1736331
  have htrace : WordTrace (prefixWord ++ tailWord_1736331) baseStart_1736331 baseEnd_1736331 := by
    simpa [prefixWord, tailWord_1736331, baseEnd_1736331] using wordTrace_append hprefix tailTrace_1736331
  have hstable : (prefixWord ++ tailWord_1736331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736331).length < 2 ^ (prefixWord ++ tailWord_1736331).sum := by decide
  have hdescent : baseEnd_1736331 < baseStart_1736331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736338 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1736338 : Nat := 118140960795 + 1736338 * 2 ^ 59
def prefixEnd_1736338 : Nat := 4983230072969 + 3 ^ 40 * 1736338 * 2
def baseEnd_1736338 : Nat := 891575972666532803289733

theorem tailTrace_1736338 : CollatzResearch.WordTrace tailWord_1736338 prefixEnd_1736338 891575972666532803289733 := by
  unfold tailWord_1736338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15832362395887860941630417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42219633055700962511014445 15832362395887860941630417)
  ·
    refine ⟨11874271796915895706222813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15832362395887860941630417 11874271796915895706222813)
    ·
      refine ⟨4452851923843460889833555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11874271796915895706222813 4452851923843460889833555)
      ·
        refine ⟨6679277885765191334750333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452851923843460889833555 6679277885765191334750333)
        ·
          refine ⟨2504729207161946750531375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6679277885765191334750333 2504729207161946750531375)
          ·
            refine ⟨3757093810742920125797063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504729207161946750531375 3757093810742920125797063)
            ·
              refine ⟨5635640716114380188695595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757093810742920125797063 5635640716114380188695595)
              ·
                refine ⟨8453461074171570283043393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635640716114380188695595 8453461074171570283043393)
                ·
                  refine ⟨6340095805628677712282545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8453461074171570283043393 6340095805628677712282545)
                  ·
                    refine ⟨4755071854221508284211909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340095805628677712282545 4755071854221508284211909)
                    ·
                      refine ⟨891575972666532803289733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4755071854221508284211909 891575972666532803289733)
                      ·
                        rfl

theorem cell23_1736338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1736338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736338 prefixEnd_1736338 := by exact prefixLift 1736338
  have htrace : WordTrace (prefixWord ++ tailWord_1736338) baseStart_1736338 baseEnd_1736338 := by
    simpa [prefixWord, tailWord_1736338, baseEnd_1736338] using wordTrace_append hprefix tailTrace_1736338
  have hstable : (prefixWord ++ tailWord_1736338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736338).length < 2 ^ (prefixWord ++ tailWord_1736338).sum := by decide
  have hdescent : baseEnd_1736338 < baseStart_1736338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736381 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1736381 : Nat := 118140960795 + 1736381 * 2 ^ 59
def prefixEnd_1736381 : Nat := 4983230072969 + 3 ^ 40 * 1736381 * 2
def baseEnd_1736381 : Nat := 891598052334676135052035

theorem tailTrace_1736381 : CollatzResearch.WordTrace tailWord_1736381 prefixEnd_1736381 891598052334676135052035 := by
  unfold tailWord_1736381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63331017922395662110336997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42220678614930441406891331 63331017922395662110336997)
  ·
    refine ⟨11874565860449186645688187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63331017922395662110336997 11874565860449186645688187)
    ·
      refine ⟨17811848790673779968532281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874565860449186645688187 17811848790673779968532281)
      ·
        refine ⟨13358886593005334976399211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17811848790673779968532281 13358886593005334976399211)
        ·
          refine ⟨20038329889508002464598817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358886593005334976399211 20038329889508002464598817)
          ·
            refine ⟨15028747417131001848449113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20038329889508002464598817 15028747417131001848449113)
            ·
              refine ⟨11271560562848251386336835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15028747417131001848449113 11271560562848251386336835)
              ·
                refine ⟨16907340844272377079505253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271560562848251386336835 16907340844272377079505253)
                ·
                  refine ⟨3170126408301070702407235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16907340844272377079505253 3170126408301070702407235)
                  ·
                    refine ⟨4755189612451606053610853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170126408301070702407235 4755189612451606053610853)
                    ·
                      refine ⟨891598052334676135052035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4755189612451606053610853 891598052334676135052035)
                      ·
                        rfl

theorem cell23_1736381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1736381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736381 prefixEnd_1736381 := by exact prefixLift 1736381
  have htrace : WordTrace (prefixWord ++ tailWord_1736381) baseStart_1736381 baseEnd_1736381 := by
    simpa [prefixWord, tailWord_1736381, baseEnd_1736381] using wordTrace_append hprefix tailTrace_1736381
  have hstable : (prefixWord ++ tailWord_1736381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736381).length < 2 ^ (prefixWord ++ tailWord_1736381).sum := by decide
  have hdescent : baseEnd_1736381 < baseStart_1736381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736398 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_1736398 : Nat := 118140960795 + 1736398 * 2 ^ 59
def prefixEnd_1736398 : Nat := 4983230072969 + 3 ^ 40 * 1736398 * 2
def baseEnd_1736398 : Nat := 891606781505802568539457

theorem tailTrace_1736398 : CollatzResearch.WordTrace tailWord_1736398 prefixEnd_1736398 891606781505802568539457 := by
  unfold tailWord_1736398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916454745416759251713231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42221091975556049342470565 7916454745416759251713231)
  ·
    refine ⟨11874682118125138877569847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7916454745416759251713231 11874682118125138877569847)
    ·
      refine ⟨17812023177187708316354771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874682118125138877569847 17812023177187708316354771)
      ·
        refine ⟨26718034765781562474532157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812023177187708316354771 26718034765781562474532157)
        ·
          refine ⟨10019263037168085927949559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26718034765781562474532157 10019263037168085927949559)
          ·
            refine ⟨15028894555752128891924339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019263037168085927949559 15028894555752128891924339)
            ·
              refine ⟨22543341833628193337886509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15028894555752128891924339 22543341833628193337886509)
              ·
                refine ⟨8453753187610572501707441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22543341833628193337886509 8453753187610572501707441)
                ·
                  refine ⟨6340314890707929376280581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8453753187610572501707441 6340314890707929376280581)
                  ·
                    refine ⟨1188809042007736758052609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6340314890707929376280581 1188809042007736758052609)
                    ·
                      refine ⟨891606781505802568539457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188809042007736758052609 891606781505802568539457)
                      ·
                        rfl

theorem cell23_1736398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_1736398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736398 prefixEnd_1736398 := by exact prefixLift 1736398
  have htrace : WordTrace (prefixWord ++ tailWord_1736398) baseStart_1736398 baseEnd_1736398 := by
    simpa [prefixWord, tailWord_1736398, baseEnd_1736398] using wordTrace_append hprefix tailTrace_1736398
  have hstable : (prefixWord ++ tailWord_1736398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736398).length < 2 ^ (prefixWord ++ tailWord_1736398).sum := by decide
  have hdescent : baseEnd_1736398 < baseStart_1736398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736401 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_1736401 : Nat := 118140960795 + 1736401 * 2 ^ 59
def prefixEnd_1736401 : Nat := 4983230072969 + 3 ^ 40 * 1736401 * 2
def baseEnd_1736401 : Nat := 891608321947766056801943

theorem tailTrace_1736401 : CollatzResearch.WordTrace tailWord_1736401 prefixEnd_1736401 891608321947766056801943 := by
  unfold tailWord_1736401
  simp only [CollatzResearch.WordTrace]
  refine ⟨63331747382323205526065057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42221164921548803684043371 63331747382323205526065057)
  ·
    refine ⟨47498810536742404144548793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63331747382323205526065057 47498810536742404144548793)
    ·
      refine ⟨35624107902556803108411595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47498810536742404144548793 35624107902556803108411595)
      ·
        refine ⟨53436161853835204662617393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35624107902556803108411595 53436161853835204662617393)
        ·
          refine ⟨40077121390376403496963045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53436161853835204662617393 40077121390376403496963045)
          ·
            refine ⟨7514460260695575655680571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40077121390376403496963045 7514460260695575655680571)
            ·
              refine ⟨11271690391043363483520857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514460260695575655680571 11271690391043363483520857)
              ·
                refine ⟨8453767793282522612640643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11271690391043363483520857 8453767793282522612640643)
                ·
                  refine ⟨12680651689923783918960965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453767793282522612640643 12680651689923783918960965)
                  ·
                    refine ⟨2377622191860709484805181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12680651689923783918960965 2377622191860709484805181)
                    ·
                      refine ⟨891608321947766056801943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377622191860709484805181 891608321947766056801943)
                      ·
                        rfl

theorem cell23_1736401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_1736401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736401 prefixEnd_1736401 := by exact prefixLift 1736401
  have htrace : WordTrace (prefixWord ++ tailWord_1736401) baseStart_1736401 baseEnd_1736401 := by
    simpa [prefixWord, tailWord_1736401, baseEnd_1736401] using wordTrace_append hprefix tailTrace_1736401
  have hstable : (prefixWord ++ tailWord_1736401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736401).length < 2 ^ (prefixWord ++ tailWord_1736401).sum := by decide
  have hdescent : baseEnd_1736401 < baseStart_1736401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736481 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1736481 : Nat := 118140960795 + 1736481 * 2 ^ 59
def prefixEnd_1736481 : Nat := 4983230072969 + 3 ^ 40 * 1736481 * 2
def baseEnd_1736481 : Nat := 297216466800041914600525

theorem tailTrace_1736481 : CollatzResearch.WordTrace tailWord_1736481 prefixEnd_1736481 297216466800041914600525 := by
  unfold tailWord_1736481
  simp only [CollatzResearch.WordTrace]
  refine ⟨63334665222033379188977297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42223110148022252792651531 63334665222033379188977297)
  ·
    refine ⟨47500998916525034391732973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63334665222033379188977297 47500998916525034391732973)
    ·
      refine ⟨17812874593696887896899865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47500998916525034391732973 17812874593696887896899865)
      ·
        refine ⟨13359655945272665922674899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17812874593696887896899865 13359655945272665922674899)
        ·
          refine ⟨20039483917908998884012349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13359655945272665922674899 20039483917908998884012349)
          ·
            refine ⟨7514806469215874581504631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20039483917908998884012349 7514806469215874581504631)
            ·
              refine ⟨11272209703823811872256947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514806469215874581504631 11272209703823811872256947)
              ·
                refine ⟨16908314555735717808385421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11272209703823811872256947 16908314555735717808385421)
                ·
                  refine ⟨6340617958400894178144533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16908314555735717808385421 6340617958400894178144533)
                  ·
                    refine ⟨297216466800041914600525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6340617958400894178144533 297216466800041914600525)
                    ·
                      rfl

theorem cell23_1736481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1736481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736481 prefixEnd_1736481 := by exact prefixLift 1736481
  have htrace : WordTrace (prefixWord ++ tailWord_1736481) baseStart_1736481 baseEnd_1736481 := by
    simpa [prefixWord, tailWord_1736481, baseEnd_1736481] using wordTrace_append hprefix tailTrace_1736481
  have hstable : (prefixWord ++ tailWord_1736481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736481).length < 2 ^ (prefixWord ++ tailWord_1736481).sum := by decide
  have hdescent : baseEnd_1736481 < baseStart_1736481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736482 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_1736482 : Nat := 118140960795 + 1736482 * 2 ^ 59
def prefixEnd_1736482 : Nat := 4983230072969 + 3 ^ 40 * 1736482 * 2
def baseEnd_1736482 : Nat := 891649913880780239889071

theorem tailTrace_1736482 : CollatzResearch.WordTrace tailWord_1736482 prefixEnd_1736482 891649913880780239889071 := by
  unfold tailWord_1736482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833675423757439089940925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42223134463353170906509133 15833675423757439089940925)
  ·
    refine ⟨5937628283909039658727847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15833675423757439089940925 5937628283909039658727847)
    ·
      refine ⟨8906442425863559488091771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937628283909039658727847 8906442425863559488091771)
      ·
        refine ⟨13359663638795339232137657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906442425863559488091771 13359663638795339232137657)
        ·
          refine ⟨10019747729096504424103243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13359663638795339232137657 10019747729096504424103243)
          ·
            refine ⟨15029621593644756636154865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019747729096504424103243 15029621593644756636154865)
            ·
              refine ⟨11272216195233567477116149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15029621593644756636154865 11272216195233567477116149)
              ·
                refine ⟨1056770268303146950979639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11272216195233567477116149 1056770268303146950979639)
                ·
                  refine ⟨1585155402454720426469459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056770268303146950979639 1585155402454720426469459)
                  ·
                    refine ⟨2377733103682080639704189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1585155402454720426469459 2377733103682080639704189)
                    ·
                      refine ⟨891649913880780239889071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377733103682080639704189 891649913880780239889071)
                      ·
                        rfl

theorem cell23_1736482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_1736482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736482 prefixEnd_1736482 := by exact prefixLift 1736482
  have htrace : WordTrace (prefixWord ++ tailWord_1736482) baseStart_1736482 baseEnd_1736482 := by
    simpa [prefixWord, tailWord_1736482, baseEnd_1736482] using wordTrace_append hprefix tailTrace_1736482
  have hstable : (prefixWord ++ tailWord_1736482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736482).length < 2 ^ (prefixWord ++ tailWord_1736482).sum := by decide
  have hdescent : baseEnd_1736482 < baseStart_1736482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736485 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_1736485 : Nat := 118140960795 + 1736485 * 2 ^ 59
def prefixEnd_1736485 : Nat := 4983230072969 + 3 ^ 40 * 1736485 * 2
def baseEnd_1736485 : Nat := 297217151440914576050519

theorem tailTrace_1736485 : CollatzResearch.WordTrace tailWord_1736485 prefixEnd_1736485 297217151440914576050519 := by
  unfold tailWord_1736485
  simp only [CollatzResearch.WordTrace]
  refine ⟨63334811114018887872122909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42223207409345925248081939 63334811114018887872122909)
  ·
    refine ⟨23750554167757082952046091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63334811114018887872122909 23750554167757082952046091)
    ·
      refine ⟨35625831251635624428069137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23750554167757082952046091 35625831251635624428069137)
      ·
        refine ⟨26719373438726718321051853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35625831251635624428069137 26719373438726718321051853)
        ·
          refine ⟨10019765039522519370394445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26719373438726718321051853 10019765039522519370394445)
          ·
            refine ⟨3757411889820944763897917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10019765039522519370394445 3757411889820944763897917)
            ·
              refine ⟨1409029458682854286461719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3757411889820944763897917 1409029458682854286461719)
              ·
                refine ⟨2113544188024281429692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409029458682854286461719 2113544188024281429692579)
                ·
                  refine ⟨3170316282036422144538869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113544188024281429692579 3170316282036422144538869)
                  ·
                    refine ⟨297217151440914576050519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3170316282036422144538869 297217151440914576050519)
                    ·
                      rfl

theorem cell23_1736485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_1736485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736485 prefixEnd_1736485 := by exact prefixLift 1736485
  have htrace : WordTrace (prefixWord ++ tailWord_1736485) baseStart_1736485 baseEnd_1736485 := by
    simpa [prefixWord, tailWord_1736485, baseEnd_1736485] using wordTrace_append hprefix tailTrace_1736485
  have hstable : (prefixWord ++ tailWord_1736485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736485).length < 2 ^ (prefixWord ++ tailWord_1736485).sum := by decide
  have hdescent : baseEnd_1736485 < baseStart_1736485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736508 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1736508 : Nat := 118140960795 + 1736508 * 2 ^ 59
def prefixEnd_1736508 : Nat := 4983230072969 + 3 ^ 40 * 1736508 * 2
def baseEnd_1736508 : Nat := 891663264377797138163951

theorem tailTrace_1736508 : CollatzResearch.WordTrace tailWord_1736508 prefixEnd_1736508 891663264377797138163951 := by
  unfold tailWord_1736508
  simp only [CollatzResearch.WordTrace]
  refine ⟨31667824996467781400105089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42223766661957041866806785 31667824996467781400105089)
  ·
    refine ⟨23750868747350836050078817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31667824996467781400105089 23750868747350836050078817)
    ·
      refine ⟨17813151560513127037559113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23750868747350836050078817 17813151560513127037559113)
      ·
        refine ⟨13359863670384845278169335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17813151560513127037559113 13359863670384845278169335)
        ·
          refine ⟨20039795505577267917254003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13359863670384845278169335 20039795505577267917254003)
          ·
            refine ⟨30059693258365901875881005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20039795505577267917254003 30059693258365901875881005)
            ·
              refine ⟨11272384971887213203455377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30059693258365901875881005 11272384971887213203455377)
              ·
                refine ⟨8454288728915409902591533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11272384971887213203455377 8454288728915409902591533)
                ·
                  refine ⟨3170358273343278713471825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8454288728915409902591533 3170358273343278713471825)
                  ·
                    refine ⟨2377768705007459035103869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3170358273343278713471825 2377768705007459035103869)
                    ·
                      refine ⟨891663264377797138163951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377768705007459035103869 891663264377797138163951)
                      ·
                        rfl

theorem cell23_1736508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1736508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736508 prefixEnd_1736508 := by exact prefixLift 1736508
  have htrace : WordTrace (prefixWord ++ tailWord_1736508) baseStart_1736508 baseEnd_1736508 := by
    simpa [prefixWord, tailWord_1736508, baseEnd_1736508] using wordTrace_append hprefix tailTrace_1736508
  have hstable : (prefixWord ++ tailWord_1736508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736508).length < 2 ^ (prefixWord ++ tailWord_1736508).sum := by decide
  have hdescent : baseEnd_1736508 < baseStart_1736508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736538 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1736538 : Nat := 118140960795 + 1736538 * 2 ^ 59
def prefixEnd_1736538 : Nat := 4983230072969 + 3 ^ 40 * 1736538 * 2
def baseEnd_1736538 : Nat := 891678668797432020788813

theorem tailTrace_1736538 : CollatzResearch.WordTrace tailWord_1736538 prefixEnd_1736538 891678668797432020788813 := by
  unfold tailWord_1736538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834186045706719480950567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42224496121884585282534845 15834186045706719480950567)
  ·
    refine ⟨23751279068560079221425851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15834186045706719480950567 23751279068560079221425851)
    ·
      refine ⟨35626918602840118832138777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23751279068560079221425851 35626918602840118832138777)
      ·
        refine ⟨26720188952130089124104083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35626918602840118832138777 26720188952130089124104083)
        ·
          refine ⟨40080283428195133686156125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26720188952130089124104083 40080283428195133686156125)
          ·
            refine ⟨15030106285573175132308547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40080283428195133686156125 15030106285573175132308547)
            ·
              refine ⟨22545159428359762698462821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15030106285573175132308547 22545159428359762698462821)
              ·
                refine ⟨4227217392817455505961779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22545159428359762698462821 4227217392817455505961779)
                ·
                  refine ⟨6340826089226183258942669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227217392817455505961779 6340826089226183258942669)
                  ·
                    refine ⟨2377809783459818722103501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6340826089226183258942669 2377809783459818722103501)
                    ·
                      refine ⟨891678668797432020788813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2377809783459818722103501 891678668797432020788813)
                      ·
                        rfl

theorem cell23_1736538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1736538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736538 prefixEnd_1736538 := by exact prefixLift 1736538
  have htrace : WordTrace (prefixWord ++ tailWord_1736538) baseStart_1736538 baseEnd_1736538 := by
    simpa [prefixWord, tailWord_1736538, baseEnd_1736538] using wordTrace_append hprefix tailTrace_1736538
  have hstable : (prefixWord ++ tailWord_1736538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736538).length < 2 ^ (prefixWord ++ tailWord_1736538).sum := by decide
  have hdescent : baseEnd_1736538 < baseStart_1736538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736590 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1736590 : Nat := 118140960795 + 1736590 * 2 ^ 59
def prefixEnd_1736590 : Nat := 4983230072969 + 3 ^ 40 * 1736590 * 2
def baseEnd_1736590 : Nat := 891705369791465817338575

theorem tailTrace_1736590 : CollatzResearch.WordTrace tailWord_1736590 prefixEnd_1736590 891705369791465817338575 := by
  unfold tailWord_1736590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917330097329811350586903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42225760519092327203130149 7917330097329811350586903)
  ·
    refine ⟨11875995145994717025880355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917330097329811350586903 11875995145994717025880355)
    ·
      refine ⟨17813992718992075538820533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11875995145994717025880355 17813992718992075538820533)
      ·
        refine ⟨1670061817405507081764425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17813992718992075538820533 1670061817405507081764425)
        ·
          refine ⟨1252546363054130311323319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670061817405507081764425 1252546363054130311323319)
          ·
            refine ⟨1878819544581195466984979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252546363054130311323319 1878819544581195466984979)
            ·
              refine ⟨2818229316871793200477469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878819544581195466984979 2818229316871793200477469)
              ·
                refine ⟨1056835993826922450179051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2818229316871793200477469 1056835993826922450179051)
                ·
                  refine ⟨1585253990740383675268577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056835993826922450179051 1585253990740383675268577)
                  ·
                    refine ⟨1188940493055287756451433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585253990740383675268577 1188940493055287756451433)
                    ·
                      refine ⟨891705369791465817338575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188940493055287756451433 891705369791465817338575)
                      ·
                        rfl

theorem cell23_1736590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1736590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736590 prefixEnd_1736590 := by exact prefixLift 1736590
  have htrace : WordTrace (prefixWord ++ tailWord_1736590) baseStart_1736590 baseEnd_1736590 := by
    simpa [prefixWord, tailWord_1736590, baseEnd_1736590] using wordTrace_append hprefix tailTrace_1736590
  have hstable : (prefixWord ++ tailWord_1736590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736590).length < 2 ^ (prefixWord ++ tailWord_1736590).sum := by decide
  have hdescent : baseEnd_1736590 < baseStart_1736590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736601 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 9]
def baseStart_1736601 : Nat := 118140960795 + 1736601 * 2 ^ 59
def prefixEnd_1736601 : Nat := 4983230072969 + 3 ^ 40 * 1736601 * 2
def baseEnd_1736601 : Nat := 99079002008740586033447

theorem tailTrace_1736601 : CollatzResearch.WordTrace tailWord_1736601 prefixEnd_1736601 99079002008740586033447 := by
  unfold tailWord_1736601
  simp only [CollatzResearch.WordTrace]
  refine ⟨63339041981598639683345657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42226027987732426455563771 63339041981598639683345657)
  ·
    refine ⟨47504281486198979762509243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63339041981598639683345657 47504281486198979762509243)
    ·
      refine ⟨71256422229298469643763865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47504281486198979762509243 71256422229298469643763865)
      ·
        refine ⟨53442316671973852232822899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71256422229298469643763865 53442316671973852232822899)
        ·
          refine ⟨80163475007960778349234349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53442316671973852232822899 80163475007960778349234349)
          ·
            refine ⟨30061303127985291880962881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80163475007960778349234349 30061303127985291880962881)
            ·
              refine ⟨22545977345988968910722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30061303127985291880962881 22545977345988968910722161)
              ·
                refine ⟨16909483009491726683041621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22545977345988968910722161 16909483009491726683041621)
                ·
                  refine ⟨99079002008740586033447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16909483009491726683041621 99079002008740586033447)
                  ·
                    rfl

theorem cell23_1736601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_1736601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736601 prefixEnd_1736601 := by exact prefixLift 1736601
  have htrace : WordTrace (prefixWord ++ tailWord_1736601) baseStart_1736601 baseEnd_1736601 := by
    simpa [prefixWord, tailWord_1736601, baseEnd_1736601] using wordTrace_append hprefix tailTrace_1736601
  have hstable : (prefixWord ++ tailWord_1736601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736601).length < 2 ^ (prefixWord ++ tailWord_1736601).sum := by decide
  have hdescent : baseEnd_1736601 < baseStart_1736601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736611 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1736611 : Nat := 118140960795 + 1736611 * 2 ^ 59
def prefixEnd_1736611 : Nat := 4983230072969 + 3 ^ 40 * 1736611 * 2
def baseEnd_1736611 : Nat := 891716152885210235175977

theorem tailTrace_1736611 : CollatzResearch.WordTrace tailWord_1736611 prefixEnd_1736611 891716152885210235175977 := by
  unfold tailWord_1736611
  simp only [CollatzResearch.WordTrace]
  refine ⟨63339406711562411391209687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42226271141041607594139791 63339406711562411391209687)
  ·
    refine ⟨95009110067343617086814531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63339406711562411391209687 95009110067343617086814531)
    ·
      refine ⟨142513665101015425630221797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95009110067343617086814531 142513665101015425630221797)
      ·
        refine ⟨26721312206440392305666587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142513665101015425630221797 26721312206440392305666587)
        ·
          refine ⟨40081968309660588458499881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26721312206440392305666587 40081968309660588458499881)
          ·
            refine ⟨30061476232245441343874911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40081968309660588458499881 30061476232245441343874911)
            ·
              refine ⟨45092214348368162015812367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30061476232245441343874911 45092214348368162015812367)
              ·
                refine ⟨67638321522552243023718551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45092214348368162015812367 67638321522552243023718551)
                ·
                  refine ⟨101457482283828364535577827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67638321522552243023718551 101457482283828364535577827)
                  ·
                    refine ⟨152186223425742546803366741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101457482283828364535577827 152186223425742546803366741)
                    ·
                      refine ⟨891716152885210235175977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 152186223425742546803366741 891716152885210235175977)
                      ·
                        rfl

theorem cell23_1736611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1736611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736611 prefixEnd_1736611 := by exact prefixLift 1736611
  have htrace : WordTrace (prefixWord ++ tailWord_1736611) baseStart_1736611 baseEnd_1736611 := by
    simpa [prefixWord, tailWord_1736611, baseEnd_1736611] using wordTrace_append hprefix tailTrace_1736611
  have hstable : (prefixWord ++ tailWord_1736611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736611).length < 2 ^ (prefixWord ++ tailWord_1736611).sum := by decide
  have hdescent : baseEnd_1736611 < baseStart_1736611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736612 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_1736612 : Nat := 118140960795 + 1736612 * 2 ^ 59
def prefixEnd_1736612 : Nat := 4983230072969 + 3 ^ 40 * 1736612 * 2
def baseEnd_1736612 : Nat := 891716666365864731263473

theorem tailTrace_1736612 : CollatzResearch.WordTrace tailWord_1736612 prefixEnd_1736612 891716666365864731263473 := by
  unfold tailWord_1736612
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669721592279394280998045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42226295456372525707997393 31669721592279394280998045)
  ·
    refine ⟨11876145597104772855374267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31669721592279394280998045 11876145597104772855374267)
    ·
      refine ⟨17814218395657159283061401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876145597104772855374267 17814218395657159283061401)
      ·
        refine ⟨13360663796742869462296051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17814218395657159283061401 13360663796742869462296051)
        ·
          refine ⟨20040995695114304193444077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360663796742869462296051 20040995695114304193444077)
          ·
            refine ⟨7515373385667864072541529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20040995695114304193444077 7515373385667864072541529)
            ·
              refine ⟨5636530039250898054406147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7515373385667864072541529 5636530039250898054406147)
              ·
                refine ⟨8454795058876347081609221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636530039250898054406147 8454795058876347081609221)
                ·
                  refine ⟨1585274073539315077801729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8454795058876347081609221 1585274073539315077801729)
                  ·
                    refine ⟨1188955555154486308351297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585274073539315077801729 1188955555154486308351297)
                    ·
                      refine ⟨891716666365864731263473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188955555154486308351297 891716666365864731263473)
                      ·
                        rfl

theorem cell23_1736612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_1736612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736612 prefixEnd_1736612 := by exact prefixLift 1736612
  have htrace : WordTrace (prefixWord ++ tailWord_1736612) baseStart_1736612 baseEnd_1736612 := by
    simpa [prefixWord, tailWord_1736612, baseEnd_1736612] using wordTrace_append hprefix tailTrace_1736612
  have hstable : (prefixWord ++ tailWord_1736612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736612).length < 2 ^ (prefixWord ++ tailWord_1736612).sum := by decide
  have hdescent : baseEnd_1736612 < baseStart_1736612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736629 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1736629 : Nat := 118140960795 + 1736629 * 2 ^ 59
def prefixEnd_1736629 : Nat := 4983230072969 + 3 ^ 40 * 1736629 * 2
def baseEnd_1736629 : Nat := 891725395536991164750895

theorem tailTrace_1736629 : CollatzResearch.WordTrace tailWord_1736629 prefixEnd_1736629 891725395536991164750895 := by
  unfold tailWord_1736629
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340063225497200465364941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42226708816998133643576627 63340063225497200465364941)
  ·
    refine ⟨23752523709561450174511853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63340063225497200465364941 23752523709561450174511853)
    ·
      refine ⟨8907196391085543815441945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23752523709561450174511853 8907196391085543815441945)
      ·
        refine ⟨6680397293314157861581459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8907196391085543815441945 6680397293314157861581459)
        ·
          refine ⟨10020595939971236792372189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680397293314157861581459 10020595939971236792372189)
          ·
            refine ⟨3757723477489213797139571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10020595939971236792372189 3757723477489213797139571)
            ·
              refine ⟨5636585216233820695709357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757723477489213797139571 5636585216233820695709357)
              ·
                refine ⟨2113719456087682760891009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5636585216233820695709357 2113719456087682760891009)
                ·
                  refine ⟨1585289592065762070668257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2113719456087682760891009 1585289592065762070668257)
                  ·
                    refine ⟨1188967194049321553001193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585289592065762070668257 1188967194049321553001193)
                    ·
                      refine ⟨891725395536991164750895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1188967194049321553001193 891725395536991164750895)
                      ·
                        rfl

theorem cell23_1736629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1736629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736629 prefixEnd_1736629 := by exact prefixLift 1736629
  have htrace : WordTrace (prefixWord ++ tailWord_1736629) baseStart_1736629 baseEnd_1736629 := by
    simpa [prefixWord, tailWord_1736629, baseEnd_1736629] using wordTrace_append hprefix tailTrace_1736629
  have hstable : (prefixWord ++ tailWord_1736629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736629).length < 2 ^ (prefixWord ++ tailWord_1736629).sum := by decide
  have hdescent : baseEnd_1736629 < baseStart_1736629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736702 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1736702 : Nat := 118140960795 + 1736702 * 2 ^ 59
def prefixEnd_1736702 : Nat := 4983230072969 + 3 ^ 40 * 1736702 * 2
def baseEnd_1736702 : Nat := 891762879624769379138059

theorem tailTrace_1736702 : CollatzResearch.WordTrace tailWord_1736702 prefixEnd_1736702 891762879624769379138059 := by
  unfold tailWord_1736702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917840719279091741596545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42228483836155155955181573 7917840719279091741596545)
  ·
    refine ⟨5938380539459318806197409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7917840719279091741596545 5938380539459318806197409)
    ·
      refine ⟨4453785404594489104648057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5938380539459318806197409 4453785404594489104648057)
      ·
        refine ⟨3340339053445866828486043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4453785404594489104648057 3340339053445866828486043)
        ·
          refine ⟨5010508580168800242729065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340339053445866828486043 5010508580168800242729065)
          ·
            refine ⟨3757881435126600182046799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5010508580168800242729065 3757881435126600182046799)
            ·
              refine ⟨5636822152689900273070199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757881435126600182046799 5636822152689900273070199)
              ·
                refine ⟨8455233229034850409605299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636822152689900273070199 8455233229034850409605299)
                ·
                  refine ⟨12682849843552275614407949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455233229034850409605299 12682849843552275614407949)
                  ·
                    refine ⟨4756068691332103355402981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12682849843552275614407949 4756068691332103355402981)
                    ·
                      refine ⟨891762879624769379138059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4756068691332103355402981 891762879624769379138059)
                      ·
                        rfl

theorem cell23_1736702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1736702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736702 prefixEnd_1736702 := by exact prefixLift 1736702
  have htrace : WordTrace (prefixWord ++ tailWord_1736702) baseStart_1736702 baseEnd_1736702 := by
    simpa [prefixWord, tailWord_1736702, baseEnd_1736702] using wordTrace_append hprefix tailTrace_1736702
  have hstable : (prefixWord ++ tailWord_1736702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736702).length < 2 ^ (prefixWord ++ tailWord_1736702).sum := by decide
  have hdescent : baseEnd_1736702 < baseStart_1736702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736705 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1736705 : Nat := 118140960795 + 1736705 * 2 ^ 59
def prefixEnd_1736705 : Nat := 4983230072969 + 3 ^ 40 * 1736705 * 2
def baseEnd_1736705 : Nat := 891764420066732867400545

theorem tailTrace_1736705 : CollatzResearch.WordTrace tailWord_1736705 prefixEnd_1736705 891764420066732867400545 := by
  unfold tailWord_1736705
  simp only [CollatzResearch.WordTrace]
  refine ⟨63342835173221865445131569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42228556782147910296754379 63342835173221865445131569)
  ·
    refine ⟨47507126379916399083848677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63342835173221865445131569 47507126379916399083848677)
    ·
      refine ⟨8907586196234324828221627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47507126379916399083848677 8907586196234324828221627)
      ·
        refine ⟨13361379294351487242332441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907586196234324828221627 13361379294351487242332441)
        ·
          refine ⟨10021034470763615431749331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13361379294351487242332441 10021034470763615431749331)
          ·
            refine ⟨15031551706145423147623997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021034470763615431749331 15031551706145423147623997)
            ·
              refine ⟨5636831889804533680358999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15031551706145423147623997 5636831889804533680358999)
              ·
                refine ⟨8455247834706800520538499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636831889804533680358999 8455247834706800520538499)
                ·
                  refine ⟨12682871752060200780807749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455247834706800520538499 12682871752060200780807749)
                  ·
                    refine ⟨2378038453511287646401453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12682871752060200780807749 2378038453511287646401453)
                    ·
                      refine ⟨891764420066732867400545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378038453511287646401453 891764420066732867400545)
                      ·
                        rfl

theorem cell23_1736705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1736705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736705 prefixEnd_1736705 := by exact prefixLift 1736705
  have htrace : WordTrace (prefixWord ++ tailWord_1736705) baseStart_1736705 baseEnd_1736705 := by
    simpa [prefixWord, tailWord_1736705, baseEnd_1736705] using wordTrace_append hprefix tailTrace_1736705
  have hstable : (prefixWord ++ tailWord_1736705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736705).length < 2 ^ (prefixWord ++ tailWord_1736705).sum := by decide
  have hdescent : baseEnd_1736705 < baseStart_1736705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736725 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 8]
def baseStart_1736725 : Nat := 118140960795 + 1736725 * 2 ^ 59
def prefixEnd_1736725 : Nat := 4983230072969 + 3 ^ 40 * 1736725 * 2
def baseEnd_1736725 : Nat := 99086076631091421016717

theorem tailTrace_1736725 : CollatzResearch.WordTrace tailWord_1736725 prefixEnd_1736725 99086076631091421016717 := by
  unfold tailWord_1736725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343564633149408860859629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42229043088766272573906419 63343564633149408860859629)
  ·
    refine ⟨23753836737431028322822361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63343564633149408860859629 23753836737431028322822361)
    ·
      refine ⟨17815377553073271242116771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23753836737431028322822361 17815377553073271242116771)
      ·
        refine ⟨26723066329609906863175157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17815377553073271242116771 26723066329609906863175157)
        ·
          refine ⟨2505287468400928768422671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26723066329609906863175157 2505287468400928768422671)
          ·
            refine ⟨3757931202601393152634007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505287468400928768422671 3757931202601393152634007)
            ·
              refine ⟨5636896803902089728951011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757931202601393152634007 5636896803902089728951011)
              ·
                refine ⟨8455345205853134593426517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636896803902089728951011 8455345205853134593426517)
                ·
                  refine ⟨99086076631091421016717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8455345205853134593426517 99086076631091421016717)
                  ·
                    rfl

theorem cell23_1736725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_1736725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736725 prefixEnd_1736725 := by exact prefixLift 1736725
  have htrace : WordTrace (prefixWord ++ tailWord_1736725) baseStart_1736725 baseEnd_1736725 := by
    simpa [prefixWord, tailWord_1736725, baseEnd_1736725] using wordTrace_append hprefix tailTrace_1736725
  have hstable : (prefixWord ++ tailWord_1736725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736725).length < 2 ^ (prefixWord ++ tailWord_1736725).sum := by decide
  have hdescent : baseEnd_1736725 < baseStart_1736725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736728 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1736728 : Nat := 118140960795 + 1736728 * 2 ^ 59
def prefixEnd_1736728 : Nat := 4983230072969 + 3 ^ 40 * 1736728 * 2
def baseEnd_1736728 : Nat := 891776230121786277412939

theorem tailTrace_1736728 : CollatzResearch.WordTrace tailWord_1736728 prefixEnd_1736728 891776230121786277412939 := by
  unfold tailWord_1736728
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671837026069270186609419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42229116034759026915479225 31671837026069270186609419)
  ·
    refine ⟨47507755539103905279914129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31671837026069270186609419 47507755539103905279914129)
    ·
      refine ⟨35630816654327928959935597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47507755539103905279914129 35630816654327928959935597)
      ·
        refine ⟨13361556245372973359975849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35630816654327928959935597 13361556245372973359975849)
        ·
          refine ⟨10021167184029730019981887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13361556245372973359975849 10021167184029730019981887)
          ·
            refine ⟨15031750776044595029972831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021167184029730019981887 15031750776044595029972831)
            ·
              refine ⟨22547626164066892544959247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031750776044595029972831 22547626164066892544959247)
              ·
                refine ⟨33821439246100338817438871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22547626164066892544959247 33821439246100338817438871)
                ·
                  refine ⟨50732158869150508226158307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33821439246100338817438871 50732158869150508226158307)
                  ·
                    refine ⟨76098238303725762339237461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50732158869150508226158307 76098238303725762339237461)
                    ·
                      refine ⟨891776230121786277412939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 76098238303725762339237461 891776230121786277412939)
                      ·
                        rfl

theorem cell23_1736728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1736728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736728 prefixEnd_1736728 := by exact prefixLift 1736728
  have htrace : WordTrace (prefixWord ++ tailWord_1736728) baseStart_1736728 baseEnd_1736728 := by
    simpa [prefixWord, tailWord_1736728, baseEnd_1736728] using wordTrace_append hprefix tailTrace_1736728
  have hstable : (prefixWord ++ tailWord_1736728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736728).length < 2 ^ (prefixWord ++ tailWord_1736728).sum := by decide
  have hdescent : baseEnd_1736728 < baseStart_1736728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736752 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_1736752 : Nat := 118140960795 + 1736752 * 2 ^ 59
def prefixEnd_1736752 : Nat := 4983230072969 + 3 ^ 40 * 1736752 * 2
def baseEnd_1736752 : Nat := 891788553657494183512829

theorem tailTrace_1736752 : CollatzResearch.WordTrace tailWord_1736752 prefixEnd_1736752 891788553657494183512829 := by
  unfold tailWord_1736752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31672274702025796236046255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42229699602701061648061673 31672274702025796236046255)
  ·
    refine ⟨47508412053038694354069383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31672274702025796236046255 47508412053038694354069383)
    ·
      refine ⟨71262618079558041531104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47508412053038694354069383 71262618079558041531104075)
      ·
        refine ⟨106893927119337062296656113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71262618079558041531104075 106893927119337062296656113)
        ·
          refine ⟨80170445339502796722492085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106893927119337062296656113 80170445339502796722492085)
          ·
            refine ⟨7515979250578387192733633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80170445339502796722492085 7515979250578387192733633)
            ·
              refine ⟨5636984437933790394550225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7515979250578387192733633 5636984437933790394550225)
              ·
                refine ⟨4227738328450342795912669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636984437933790394550225 4227738328450342795912669)
                ·
                  refine ⟨1585401873168878548467251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4227738328450342795912669 1585401873168878548467251)
                  ·
                    refine ⟨2378102809753317822700877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1585401873168878548467251 2378102809753317822700877)
                    ·
                      refine ⟨891788553657494183512829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378102809753317822700877 891788553657494183512829)
                      ·
                        rfl

theorem cell23_1736752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_1736752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736752 prefixEnd_1736752 := by exact prefixLift 1736752
  have htrace : WordTrace (prefixWord ++ tailWord_1736752) baseStart_1736752 baseEnd_1736752 := by
    simpa [prefixWord, tailWord_1736752, baseEnd_1736752] using wordTrace_append hprefix tailTrace_1736752
  have hstable : (prefixWord ++ tailWord_1736752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736752).length < 2 ^ (prefixWord ++ tailWord_1736752).sum := by decide
  have hdescent : baseEnd_1736752 < baseStart_1736752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736755 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 1, 5]
def baseStart_1736755 : Nat := 118140960795 + 1736755 * 2 ^ 59
def prefixEnd_1736755 : Nat := 4983230072969 + 3 ^ 40 * 1736755 * 2
def baseEnd_1736755 : Nat := 297263364699819223925105

theorem tailTrace_1736755 : CollatzResearch.WordTrace tailWord_1736755 prefixEnd_1736755 297263364699819223925105 := by
  unfold tailWord_1736755
  simp only [CollatzResearch.WordTrace]
  refine ⟨63344658823040723984451719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42229772548693815989634479 63344658823040723984451719)
  ·
    refine ⟨95016988234561085976677579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63344658823040723984451719 95016988234561085976677579)
    ·
      refine ⟨142525482351841628965016369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95016988234561085976677579 142525482351841628965016369)
      ·
        refine ⟨106894111763881221723762277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142525482351841628965016369 106894111763881221723762277)
        ·
          refine ⟨20042645955727729073205427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106894111763881221723762277 20042645955727729073205427)
          ·
            refine ⟨30063968933591593609808141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20042645955727729073205427 30063968933591593609808141)
            ·
              refine ⟨11273988350096847603678053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30063968933591593609808141 11273988350096847603678053)
              ·
                refine ⟨2113872815643158925689635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11273988350096847603678053 2113872815643158925689635)
                ·
                  refine ⟨3170809223464738388534453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113872815643158925689635 3170809223464738388534453)
                  ·
                    refine ⟨297263364699819223925105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3170809223464738388534453 297263364699819223925105)
                    ·
                      rfl

theorem cell23_1736755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 5].length) (baseStart_1736755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736755 prefixEnd_1736755 := by exact prefixLift 1736755
  have htrace : WordTrace (prefixWord ++ tailWord_1736755) baseStart_1736755 baseEnd_1736755 := by
    simpa [prefixWord, tailWord_1736755, baseEnd_1736755] using wordTrace_append hprefix tailTrace_1736755
  have hstable : (prefixWord ++ tailWord_1736755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736755).length < 2 ^ (prefixWord ++ tailWord_1736755).sum := by decide
  have hdescent : baseEnd_1736755 < baseStart_1736755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736762 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_1736762 : Nat := 118140960795 + 1736762 * 2 ^ 59
def prefixEnd_1736762 : Nat := 4983230072969 + 3 ^ 40 * 1736762 * 2
def baseEnd_1736762 : Nat := 891793688464039144387783

theorem tailTrace_1736762 : CollatzResearch.WordTrace tailWord_1736762 prefixEnd_1736762 891793688464039144387783 := by
  unfold tailWord_1736762
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836228533503841044989135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42229942756010242786637693 15836228533503841044989135)
  ·
    refine ⟨23754342800255761567483703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15836228533503841044989135 23754342800255761567483703)
    ·
      refine ⟨35631514200383642351225555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23754342800255761567483703 35631514200383642351225555)
      ·
        refine ⟨53447271300575463526838333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35631514200383642351225555 53447271300575463526838333)
        ·
          refine ⟨20042726737715798822564375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53447271300575463526838333 20042726737715798822564375)
          ·
            refine ⟨30064090106573698233846563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20042726737715798822564375 30064090106573698233846563)
            ·
              refine ⟨45096135159860547350769845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30064090106573698233846563 45096135159860547350769845)
              ·
                refine ⟨4227762671236926314134673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45096135159860547350769845 4227762671236926314134673)
                ·
                  refine ⟨3170822003427694735601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227762671236926314134673 3170822003427694735601005)
                  ·
                    refine ⟨1189058251285385525850377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3170822003427694735601005 1189058251285385525850377)
                    ·
                      refine ⟨891793688464039144387783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189058251285385525850377 891793688464039144387783)
                      ·
                        rfl

theorem cell23_1736762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_1736762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736762 prefixEnd_1736762 := by exact prefixLift 1736762
  have htrace : WordTrace (prefixWord ++ tailWord_1736762) baseStart_1736762 baseEnd_1736762 := by
    simpa [prefixWord, tailWord_1736762, baseEnd_1736762] using wordTrace_append hprefix tailTrace_1736762
  have hstable : (prefixWord ++ tailWord_1736762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736762).length < 2 ^ (prefixWord ++ tailWord_1736762).sum := by decide
  have hdescent : baseEnd_1736762 < baseStart_1736762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736786 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1736786 : Nat := 118140960795 + 1736786 * 2 ^ 59
def prefixEnd_1736786 : Nat := 4983230072969 + 3 ^ 40 * 1736786 * 2
def baseEnd_1736786 : Nat := 891806011999747050487673

theorem tailTrace_1736786 : CollatzResearch.WordTrace tailWord_1736786 prefixEnd_1736786 891806011999747050487673 := by
  unfold tailWord_1736786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836447371482104069707553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42230526323952277519220141 15836447371482104069707553)
  ·
    refine ⟨11877335528611578052280665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15836447371482104069707553 11877335528611578052280665)
    ·
      refine ⟨8908001646458683539210499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11877335528611578052280665 8908001646458683539210499)
      ·
        refine ⟨13362002469688025308815749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908001646458683539210499 13362002469688025308815749)
        ·
          refine ⟨2505375463066504745402953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13362002469688025308815749 2505375463066504745402953)
          ·
            refine ⟨1879031597299878559052215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505375463066504745402953 1879031597299878559052215)
            ·
              refine ⟨2818547395949817838578323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879031597299878559052215 2818547395949817838578323)
              ·
                refine ⟨4227821093924726757867485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818547395949817838578323 4227821093924726757867485)
                ·
                  refine ⟨1585432910221772534200307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4227821093924726757867485 1585432910221772534200307)
                  ·
                    refine ⟨2378149365332658801300461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1585432910221772534200307 2378149365332658801300461)
                    ·
                      refine ⟨891806011999747050487673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378149365332658801300461 891806011999747050487673)
                      ·
                        rfl

theorem cell23_1736786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1736786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736786 prefixEnd_1736786 := by exact prefixLift 1736786
  have htrace : WordTrace (prefixWord ++ tailWord_1736786) baseStart_1736786 baseEnd_1736786 := by
    simpa [prefixWord, tailWord_1736786, baseEnd_1736786] using wordTrace_append hprefix tailTrace_1736786
  have hstable : (prefixWord ++ tailWord_1736786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736786).length < 2 ^ (prefixWord ++ tailWord_1736786).sum := by decide
  have hdescent : baseEnd_1736786 < baseStart_1736786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736805 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1736805 : Nat := 118140960795 + 1736805 * 2 ^ 59
def prefixEnd_1736805 : Nat := 4983230072969 + 3 ^ 40 * 1736805 * 2
def baseEnd_1736805 : Nat := 891815768132182476150085

theorem tailTrace_1736805 : CollatzResearch.WordTrace tailWord_1736805 prefixEnd_1736805 891815768132182476150085 := by
  unfold tailWord_1736805
  simp only [CollatzResearch.WordTrace]
  refine ⟨63346482472859582523771869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42230988315239721682514579 63346482472859582523771869)
  ·
    refine ⟨23754930927322343446414451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63346482472859582523771869 23754930927322343446414451)
    ·
      refine ⟨35632396390983515169621677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23754930927322343446414451 35632396390983515169621677)
      ·
        refine ⟨13362148646618818188608129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35632396390983515169621677 13362148646618818188608129)
        ·
          refine ⟨10021611484964113641456097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13362148646618818188608129 10021611484964113641456097)
          ·
            refine ⟨7516208613723085231092073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021611484964113641456097 7516208613723085231092073)
            ·
              refine ⟨5637156460292313923319055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516208613723085231092073 5637156460292313923319055)
              ·
                refine ⟨8455734690438470884978583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637156460292313923319055 8455734690438470884978583)
                ·
                  refine ⟨12683602035657706327467875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455734690438470884978583 12683602035657706327467875)
                  ·
                    refine ⟨19025403053486559491201813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12683602035657706327467875 19025403053486559491201813)
                    ·
                      refine ⟨891815768132182476150085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19025403053486559491201813 891815768132182476150085)
                      ·
                        rfl

theorem cell23_1736805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1736805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736805 prefixEnd_1736805 := by exact prefixLift 1736805
  have htrace : WordTrace (prefixWord ++ tailWord_1736805) baseStart_1736805 baseEnd_1736805 := by
    simpa [prefixWord, tailWord_1736805, baseEnd_1736805] using wordTrace_append hprefix tailTrace_1736805
  have hstable : (prefixWord ++ tailWord_1736805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736805).length < 2 ^ (prefixWord ++ tailWord_1736805).sum := by decide
  have hdescent : baseEnd_1736805 < baseStart_1736805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736812 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1736812 : Nat := 118140960795 + 1736812 * 2 ^ 59
def prefixEnd_1736812 : Nat := 4983230072969 + 3 ^ 40 * 1736812 * 2
def baseEnd_1736812 : Nat := 891819362496763948762553

theorem tailTrace_1736812 : CollatzResearch.WordTrace tailWord_1736812 prefixEnd_1736812 891819362496763948762553 := by
  unfold tailWord_1736812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673368891917111359638345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42231158522556148479517793 31673368891917111359638345)
  ·
    refine ⟨23755026668937833519728759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31673368891917111359638345 23755026668937833519728759)
    ·
      refine ⟨35632540003406750279593139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23755026668937833519728759 35632540003406750279593139)
      ·
        refine ⟨53448810005110125419389709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35632540003406750279593139 53448810005110125419389709)
        ·
          refine ⟨20043303751916297032271141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53448810005110125419389709 20043303751916297032271141)
          ·
            refine ⟨3758119453484305693550839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20043303751916297032271141 3758119453484305693550839)
            ·
              refine ⟨5637179180226458540326259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758119453484305693550839 5637179180226458540326259)
              ·
                refine ⟨8455768770339687810489389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637179180226458540326259 8455768770339687810489389)
                ·
                  refine ⟨3170913288877382928933521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8455768770339687810489389 3170913288877382928933521)
                  ·
                    refine ⟨2378184966658037196700141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3170913288877382928933521 2378184966658037196700141)
                    ·
                      refine ⟨891819362496763948762553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378184966658037196700141 891819362496763948762553)
                      ·
                        rfl

theorem cell23_1736812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1736812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736812 prefixEnd_1736812 := by exact prefixLift 1736812
  have htrace : WordTrace (prefixWord ++ tailWord_1736812) baseStart_1736812 baseEnd_1736812 := by
    simpa [prefixWord, tailWord_1736812, baseEnd_1736812] using wordTrace_append hprefix tailTrace_1736812
  have hstable : (prefixWord ++ tailWord_1736812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736812).length < 2 ^ (prefixWord ++ tailWord_1736812).sum := by decide
  have hdescent : baseEnd_1736812 < baseStart_1736812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736822 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1736822 : Nat := 118140960795 + 1736822 * 2 ^ 59
def prefixEnd_1736822 : Nat := 4983230072969 + 3 ^ 40 * 1736822 * 2
def baseEnd_1736822 : Nat := 891824497303308909637507

theorem tailTrace_1736822 : CollatzResearch.WordTrace tailWord_1736822 prefixEnd_1736822 891824497303308909637507 := by
  unfold tailWord_1736822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959193907112374651696295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42231401675865329618093813 3959193907112374651696295)
  ·
    refine ⟨5938790860668561977544443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959193907112374651696295 5938790860668561977544443)
    ·
      refine ⟨8908186291002842966316665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938790860668561977544443 8908186291002842966316665)
      ·
        refine ⟨6681139718252132224737499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8908186291002842966316665 6681139718252132224737499)
        ·
          refine ⟨10021709577378198337106249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681139718252132224737499 10021709577378198337106249)
          ·
            refine ⟨7516282183033648752829687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021709577378198337106249 7516282183033648752829687)
            ·
              refine ⟨11274423274550473129244531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516282183033648752829687 11274423274550473129244531)
              ·
                refine ⟨16911634911825709693866797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11274423274550473129244531 16911634911825709693866797)
                ·
                  refine ⟨6341863091934641135200049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16911634911825709693866797 6341863091934641135200049)
                  ·
                    refine ⟨4756397318950980851400037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341863091934641135200049 4756397318950980851400037)
                    ·
                      refine ⟨891824497303308909637507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4756397318950980851400037 891824497303308909637507)
                      ·
                        rfl

theorem cell23_1736822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1736822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736822 prefixEnd_1736822 := by exact prefixLift 1736822
  have htrace : WordTrace (prefixWord ++ tailWord_1736822) baseStart_1736822 baseEnd_1736822 := by
    simpa [prefixWord, tailWord_1736822, baseEnd_1736822] using wordTrace_append hprefix tailTrace_1736822
  have hstable : (prefixWord ++ tailWord_1736822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736822).length < 2 ^ (prefixWord ++ tailWord_1736822).sum := by decide
  have hdescent : baseEnd_1736822 < baseStart_1736822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736869 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_1736869 : Nat := 118140960795 + 1736869 * 2 ^ 59
def prefixEnd_1736869 : Nat := 4983230072969 + 3 ^ 40 * 1736869 * 2
def baseEnd_1736869 : Nat := 891848630894070225749791

theorem tailTrace_1736869 : CollatzResearch.WordTrace tailWord_1736869 prefixEnd_1736869 891848630894070225749791 := by
  unfold tailWord_1736869
  simp only [CollatzResearch.WordTrace]
  refine ⟨63348816744627721454101661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42232544496418480969401107 63348816744627721454101661)
  ·
    refine ⟨23755806279235395545288123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63348816744627721454101661 23755806279235395545288123)
    ·
      refine ⟨35633709418853093317932185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23755806279235395545288123 35633709418853093317932185)
      ·
        refine ⟨26725282064139819988449139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35633709418853093317932185 26725282064139819988449139)
        ·
          refine ⟨40087923096209729982673709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26725282064139819988449139 40087923096209729982673709)
          ·
            refine ⟨15032971161078648743502641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40087923096209729982673709 15032971161078648743502641)
            ·
              refine ⟨11274728370808986557626981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15032971161078648743502641 11274728370808986557626981)
              ·
                refine ⟨2114011569526684979555059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11274728370808986557626981 2114011569526684979555059)
                ·
                  refine ⟨3171017354290027469332589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114011569526684979555059 3171017354290027469332589)
                  ·
                    refine ⟨1189131507858760300999721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171017354290027469332589 1189131507858760300999721)
                    ·
                      refine ⟨891848630894070225749791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189131507858760300999721 891848630894070225749791)
                      ·
                        rfl

theorem cell23_1736869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_1736869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736869 prefixEnd_1736869 := by exact prefixLift 1736869
  have htrace : WordTrace (prefixWord ++ tailWord_1736869) baseStart_1736869 baseEnd_1736869 := by
    simpa [prefixWord, tailWord_1736869, baseEnd_1736869] using wordTrace_append hprefix tailTrace_1736869
  have hstable : (prefixWord ++ tailWord_1736869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736869).length < 2 ^ (prefixWord ++ tailWord_1736869).sum := by decide
  have hdescent : baseEnd_1736869 < baseStart_1736869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736955 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_1736955 : Nat := 118140960795 + 1736955 * 2 ^ 59
def prefixEnd_1736955 : Nat := 4983230072969 + 3 ^ 40 * 1736955 * 2
def baseEnd_1736955 : Nat := 891892790230356889274395

theorem tailTrace_1736955 : CollatzResearch.WordTrace tailWord_1736955 prefixEnd_1736955 891892790230356889274395 := by
  unfold tailWord_1736955
  simp only [CollatzResearch.WordTrace]
  refine ⟨63351953422316158141732319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42234635614877438761154879 63351953422316158141732319)
  ·
    refine ⟨95027930133474237212598479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63351953422316158141732319 95027930133474237212598479)
    ·
      refine ⟨142541895200211355818897719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95027930133474237212598479 142541895200211355818897719)
      ·
        refine ⟨213812842800317033728346579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142541895200211355818897719 213812842800317033728346579)
        ·
          refine ⟨320719264200475550592519869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213812842800317033728346579 320719264200475550592519869)
          ·
            refine ⟨120269724075178331472194951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320719264200475550592519869 120269724075178331472194951)
            ·
              refine ⟨180404586112767497208292427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120269724075178331472194951 180404586112767497208292427)
              ·
                refine ⟨270606879169151245812438641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180404586112767497208292427 270606879169151245812438641)
                ·
                  refine ⟨202955159376863434359328981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270606879169151245812438641 202955159376863434359328981)
                  ·
                    refine ⟨4756761547895236742796773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202955159376863434359328981 4756761547895236742796773)
                    ·
                      refine ⟨891892790230356889274395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4756761547895236742796773 891892790230356889274395)
                      ·
                        rfl

theorem cell23_1736955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_1736955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736955 prefixEnd_1736955 := by exact prefixLift 1736955
  have htrace : WordTrace (prefixWord ++ tailWord_1736955) baseStart_1736955 baseEnd_1736955 := by
    simpa [prefixWord, tailWord_1736955, baseEnd_1736955] using wordTrace_append hprefix tailTrace_1736955
  have hstable : (prefixWord ++ tailWord_1736955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736955).length < 2 ^ (prefixWord ++ tailWord_1736955).sum := by decide
  have hdescent : baseEnd_1736955 < baseStart_1736955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736956 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 5]
def baseStart_1736956 : Nat := 118140960795 + 1736956 * 2 ^ 59
def prefixEnd_1736956 : Nat := 4983230072969 + 3 ^ 40 * 1736956 * 2
def baseEnd_1736956 : Nat := 99099255967890153929099

theorem tailTrace_1736956 : CollatzResearch.WordTrace tailWord_1736956 prefixEnd_1736956 99099255967890153929099 := by
  unfold tailWord_1736956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31675994947656267656259361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42234659930208356875012481 31675994947656267656259361)
  ·
    refine ⟨23756996210742200742194521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31675994947656267656259361 23756996210742200742194521)
    ·
      refine ⟨17817747158056650556645891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23756996210742200742194521 17817747158056650556645891)
      ·
        refine ⟨26726620737084975834968837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17817747158056650556645891 26726620737084975834968837)
        ·
          refine ⟨5011241388203432969056657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26726620737084975834968837 5011241388203432969056657)
          ·
            refine ⟨3758431041152574726792493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5011241388203432969056657 3758431041152574726792493)
            ·
              refine ⟨1409411640432215522547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3758431041152574726792493 1409411640432215522547185)
              ·
                refine ⟨1057058730324161641910389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409411640432215522547185 1057058730324161641910389)
                ·
                  refine ⟨99099255967890153929099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057058730324161641910389 99099255967890153929099)
                  ·
                    rfl

theorem cell23_1736956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_1736956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736956 prefixEnd_1736956 := by exact prefixLift 1736956
  have htrace : WordTrace (prefixWord ++ tailWord_1736956) baseStart_1736956 baseEnd_1736956 := by
    simpa [prefixWord, tailWord_1736956, baseEnd_1736956] using wordTrace_append hprefix tailTrace_1736956
  have hstable : (prefixWord ++ tailWord_1736956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736956).length < 2 ^ (prefixWord ++ tailWord_1736956).sum := by decide
  have hdescent : baseEnd_1736956 < baseStart_1736956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736965 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1736965 : Nat := 118140960795 + 1736965 * 2 ^ 59
def prefixEnd_1736965 : Nat := 4983230072969 + 3 ^ 40 * 1736965 * 2
def baseEnd_1736965 : Nat := 297299308345633950049783

theorem tailTrace_1736965 : CollatzResearch.WordTrace tailWord_1736965 prefixEnd_1736965 297299308345633950049783 := by
  unfold tailWord_1736965
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352318152279929849596349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42234878768186619899730899 63352318152279929849596349)
  ·
    refine ⟨23757119307104973693598631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63352318152279929849596349 23757119307104973693598631)
    ·
      refine ⟨35635678960657460540397947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23757119307104973693598631 35635678960657460540397947)
      ·
        refine ⟨53453518440986190810596921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35635678960657460540397947 53453518440986190810596921)
        ·
          refine ⟨40090138830739643107947691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53453518440986190810596921 40090138830739643107947691)
          ·
            refine ⟨60135208246109464661921537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40090138830739643107947691 60135208246109464661921537)
            ·
              refine ⟨45101406184582098496441153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60135208246109464661921537 45101406184582098496441153)
              ·
                refine ⟨33826054638436573872330865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45101406184582098496441153 33826054638436573872330865)
                ·
                  refine ⟨25369540978827430404248149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33826054638436573872330865 25369540978827430404248149)
                  ·
                    refine ⟨297299308345633950049783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25369540978827430404248149 297299308345633950049783)
                    ·
                      rfl

theorem cell23_1736965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1736965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736965 prefixEnd_1736965 := by exact prefixLift 1736965
  have htrace : WordTrace (prefixWord ++ tailWord_1736965) baseStart_1736965 baseEnd_1736965 := by
    simpa [prefixWord, tailWord_1736965, baseEnd_1736965] using wordTrace_append hprefix tailTrace_1736965
  have hstable : (prefixWord ++ tailWord_1736965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736965).length < 2 ^ (prefixWord ++ tailWord_1736965).sum := by decide
  have hdescent : baseEnd_1736965 < baseStart_1736965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736967 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1736967 : Nat := 118140960795 + 1736967 * 2 ^ 59
def prefixEnd_1736967 : Nat := 4983230072969 + 3 ^ 40 * 1736967 * 2
def baseEnd_1736967 : Nat := 891898951998210842324341

theorem tailTrace_1736967 : CollatzResearch.WordTrace tailWord_1736967 prefixEnd_1736967 891898951998210842324341 := by
  unfold tailWord_1736967
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352391098272684191169155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42234927398848456127446103 63352391098272684191169155)
  ·
    refine ⟨95028586647409026286753733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63352391098272684191169155 95028586647409026286753733)
    ·
      refine ⟨17817859996389192428766325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95028586647409026286753733 17817859996389192428766325)
      ·
        refine ⟨1670424374661486790196843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17817859996389192428766325 1670424374661486790196843)
        ·
          refine ⟨2505636561992230185295265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670424374661486790196843 2505636561992230185295265)
          ·
            refine ⟨1879227421494172638971449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505636561992230185295265 1879227421494172638971449)
            ·
              refine ⟨1409420566120629479228587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879227421494172638971449 1409420566120629479228587)
              ·
                refine ⟨2114130849180944218842881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409420566120629479228587 2114130849180944218842881)
                ·
                  refine ⟨1585598136885708164132161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114130849180944218842881 1585598136885708164132161)
                  ·
                    refine ⟨1189198602664281123099121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585598136885708164132161 1189198602664281123099121)
                    ·
                      refine ⟨891898951998210842324341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189198602664281123099121 891898951998210842324341)
                      ·
                        rfl

theorem cell23_1736967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1736967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736967 prefixEnd_1736967 := by exact prefixLift 1736967
  have htrace : WordTrace (prefixWord ++ tailWord_1736967) baseStart_1736967 baseEnd_1736967 := by
    simpa [prefixWord, tailWord_1736967, baseEnd_1736967] using wordTrace_append hprefix tailTrace_1736967
  have hstable : (prefixWord ++ tailWord_1736967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736967).length < 2 ^ (prefixWord ++ tailWord_1736967).sum := by decide
  have hdescent : baseEnd_1736967 < baseStart_1736967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736972 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1736972 : Nat := 118140960795 + 1736972 * 2 ^ 59
def prefixEnd_1736972 : Nat := 4983230072969 + 3 ^ 40 * 1736972 * 2
def baseEnd_1736972 : Nat := 891901519401483322761817

theorem tailTrace_1736972 : CollatzResearch.WordTrace tailWord_1736972 prefixEnd_1736972 891901519401483322761817 := by
  unfold tailWord_1736972
  simp only [CollatzResearch.WordTrace]
  refine ⟨31676286731627285022550585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42235048975503046696734113 31676286731627285022550585)
  ·
    refine ⟨23757215048720463766912939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31676286731627285022550585 23757215048720463766912939)
    ·
      refine ⟨35635822573080695650369409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23757215048720463766912939 35635822573080695650369409)
      ·
        refine ⟨26726866929810521737777057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35635822573080695650369409 26726866929810521737777057)
        ·
          refine ⟨20045150197357891303332793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26726866929810521737777057 20045150197357891303332793)
          ·
            refine ⟨15033862648018418477499595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20045150197357891303332793 15033862648018418477499595)
            ·
              refine ⟨22550793972027627716249393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15033862648018418477499595 22550793972027627716249393)
              ·
                refine ⟨16913095479020720787187045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22550793972027627716249393 16913095479020720787187045)
                ·
                  refine ⟨3171205402316385147597571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16913095479020720787187045 3171205402316385147597571)
                  ·
                    refine ⟨4756808103474577721396357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171205402316385147597571 4756808103474577721396357)
                    ·
                      refine ⟨891901519401483322761817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4756808103474577721396357 891901519401483322761817)
                      ·
                        rfl

theorem cell23_1736972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1736972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736972 prefixEnd_1736972 := by exact prefixLift 1736972
  have htrace : WordTrace (prefixWord ++ tailWord_1736972) baseStart_1736972 baseEnd_1736972 := by
    simpa [prefixWord, tailWord_1736972, baseEnd_1736972] using wordTrace_append hprefix tailTrace_1736972
  have hstable : (prefixWord ++ tailWord_1736972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736972).length < 2 ^ (prefixWord ++ tailWord_1736972).sum := by decide
  have hdescent : baseEnd_1736972 < baseStart_1736972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736975 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_1736975 : Nat := 118140960795 + 1736975 * 2 ^ 59
def prefixEnd_1736975 : Nat := 4983230072969 + 3 ^ 40 * 1736975 * 2
def baseEnd_1736975 : Nat := 891903059843446811024303

theorem tailTrace_1736975 : CollatzResearch.WordTrace tailWord_1736975 prefixEnd_1736975 891903059843446811024303 := by
  unfold tailWord_1736975
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352682882243701557460379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42235121921495801038306919 63352682882243701557460379)
  ·
    refine ⟨95029024323365552336190569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63352682882243701557460379 95029024323365552336190569)
    ·
      refine ⟨71271768242524164252142927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95029024323365552336190569 71271768242524164252142927)
      ·
        refine ⟨106907652363786246378214391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71271768242524164252142927 106907652363786246378214391)
        ·
          refine ⟨160361478545679369567321587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106907652363786246378214391 160361478545679369567321587)
          ·
            refine ⟨240542217818519054350982381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160361478545679369567321587 240542217818519054350982381)
            ·
              refine ⟨90203331681944645381618393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240542217818519054350982381 90203331681944645381618393)
              ·
                refine ⟨67652498761458484036213795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90203331681944645381618393 67652498761458484036213795)
                ·
                  refine ⟨101478748142187726054320693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67652498761458484036213795 101478748142187726054320693)
                  ·
                    refine ⟨9513632638330099317592565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101478748142187726054320693 9513632638330099317592565)
                    ·
                      refine ⟨891903059843446811024303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9513632638330099317592565 891903059843446811024303)
                      ·
                        rfl

theorem cell23_1736975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_1736975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1736975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1736975 prefixEnd_1736975 := by exact prefixLift 1736975
  have htrace : WordTrace (prefixWord ++ tailWord_1736975) baseStart_1736975 baseEnd_1736975 := by
    simpa [prefixWord, tailWord_1736975, baseEnd_1736975] using wordTrace_append hprefix tailTrace_1736975
  have hstable : (prefixWord ++ tailWord_1736975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736975).length < 2 ^ (prefixWord ++ tailWord_1736975).sum := by decide
  have hdescent : baseEnd_1736975 < baseStart_1736975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737059 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 1, 5]
def baseStart_1737059 : Nat := 118140960795 + 1737059 * 2 ^ 59
def prefixEnd_1737059 : Nat := 4983230072969 + 3 ^ 40 * 1737059 * 2
def baseEnd_1737059 : Nat := 297315397406141494124639

theorem tailTrace_1737059 : CollatzResearch.WordTrace tailWord_1737059 prefixEnd_1737059 297315397406141494124639 := by
  unfold tailWord_1737059
  simp only [CollatzResearch.WordTrace]
  refine ⟨63355746613939383903518231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42237164409292922602345487 63355746613939383903518231)
  ·
    refine ⟨95033619920909075855277347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63355746613939383903518231 95033619920909075855277347)
    ·
      refine ⟨142550429881363613782916021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95033619920909075855277347 142550429881363613782916021)
      ·
        refine ⟨13364102801377838792148377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142550429881363613782916021 13364102801377838792148377)
        ·
          refine ⟨10023077101033379094111283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13364102801377838792148377 10023077101033379094111283)
          ·
            refine ⟨15034615651550068641166925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023077101033379094111283 15034615651550068641166925)
            ·
              refine ⟨5637980869331275740437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15034615651550068641166925 5637980869331275740437597)
              ·
                refine ⟨2114242825999228402664099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5637980869331275740437597 2114242825999228402664099)
                ·
                  refine ⟨3171364238998842603996149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114242825999228402664099 3171364238998842603996149)
                  ·
                    refine ⟨297315397406141494124639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3171364238998842603996149 297315397406141494124639)
                    ·
                      rfl

theorem cell23_1737059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 5].length) (baseStart_1737059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737059 prefixEnd_1737059 := by exact prefixLift 1737059
  have htrace : WordTrace (prefixWord ++ tailWord_1737059) baseStart_1737059 baseEnd_1737059 := by
    simpa [prefixWord, tailWord_1737059, baseEnd_1737059] using wordTrace_append hprefix tailTrace_1737059
  have hstable : (prefixWord ++ tailWord_1737059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737059).length < 2 ^ (prefixWord ++ tailWord_1737059).sum := by decide
  have hdescent : baseEnd_1737059 < baseStart_1737059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737096 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1737096 : Nat := 118140960795 + 1737096 * 2 ^ 59
def prefixEnd_1737096 : Nat := 4983230072969 + 3 ^ 40 * 1737096 * 2
def baseEnd_1737096 : Nat := 891965191002640837611247

theorem tailTrace_1737096 : CollatzResearch.WordTrace tailWord_1737096 prefixEnd_1737096 891965191002640837611247 := by
  unfold tailWord_1737096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31678548057402669611307571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42238064076536892815076761 31678548057402669611307571)
  ·
    refine ⟨47517822086104004416961357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31678548057402669611307571 47517822086104004416961357)
    ·
      refine ⟨17819183282289001656360509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47517822086104004416961357 17819183282289001656360509)
      ·
        refine ⟨6682193730858375621135191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17819183282289001656360509 6682193730858375621135191)
        ·
          refine ⟨10023290596287563431702787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682193730858375621135191 10023290596287563431702787)
          ·
            refine ⟨15034935894431345147554181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023290596287563431702787 15034935894431345147554181)
            ·
              refine ⟨2819050480205877215166409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15034935894431345147554181 2819050480205877215166409)
              ·
                refine ⟨2114287860154407911374807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819050480205877215166409 2114287860154407911374807)
                ·
                  refine ⟨3171431790231611867062211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114287860154407911374807 3171431790231611867062211)
                  ·
                    refine ⟨4757147685347417800593317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171431790231611867062211 4757147685347417800593317)
                    ·
                      refine ⟨891965191002640837611247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4757147685347417800593317 891965191002640837611247)
                      ·
                        rfl

theorem cell23_1737096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1737096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737096 prefixEnd_1737096 := by exact prefixLift 1737096
  have htrace : WordTrace (prefixWord ++ tailWord_1737096) baseStart_1737096 baseEnd_1737096 := by
    simpa [prefixWord, tailWord_1737096, baseEnd_1737096] using wordTrace_append hprefix tailTrace_1737096
  have hstable : (prefixWord ++ tailWord_1737096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737096).length < 2 ^ (prefixWord ++ tailWord_1737096).sum := by decide
  have hdescent : baseEnd_1737096 < baseStart_1737096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737132 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_1737132 : Nat := 118140960795 + 1737132 * 2 ^ 59
def prefixEnd_1737132 : Nat := 4983230072969 + 3 ^ 40 * 1737132 * 2
def baseEnd_1737132 : Nat := 297327892102067565587027

theorem tailTrace_1737132 : CollatzResearch.WordTrace tailWord_1737132 prefixEnd_1737132 297327892102067565587027 := by
  unfold tailWord_1737132
  simp only [CollatzResearch.WordTrace]
  refine ⟨31679204571337458685462825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42238939428449944913950433 31679204571337458685462825)
  ·
    refine ⟨23759403428503094014097119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31679204571337458685462825 23759403428503094014097119)
    ·
      refine ⟨35639105142754641021145679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23759403428503094014097119 35639105142754641021145679)
      ·
        refine ⟨53458657714131961531718519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639105142754641021145679 53458657714131961531718519)
        ·
          refine ⟨80187986571197942297577779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53458657714131961531718519 80187986571197942297577779)
          ·
            refine ⟨120281979856796913446366669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80187986571197942297577779 120281979856796913446366669)
            ·
              refine ⟨45105742446298842542387501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120281979856796913446366669 45105742446298842542387501)
              ·
                refine ⟨16914653417362065953395313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45105742446298842542387501 16914653417362065953395313)
                ·
                  refine ⟨12685990063021549465046485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16914653417362065953395313 12685990063021549465046485)
                  ·
                    refine ⟨297327892102067565587027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12685990063021549465046485 297327892102067565587027)
                    ·
                      rfl

theorem cell23_1737132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_1737132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737132 prefixEnd_1737132 := by exact prefixLift 1737132
  have htrace : WordTrace (prefixWord ++ tailWord_1737132) baseStart_1737132 baseEnd_1737132 := by
    simpa [prefixWord, tailWord_1737132, baseEnd_1737132] using wordTrace_append hprefix tailTrace_1737132
  have hstable : (prefixWord ++ tailWord_1737132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737132).length < 2 ^ (prefixWord ++ tailWord_1737132).sum := by decide
  have hdescent : baseEnd_1737132 < baseStart_1737132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737139 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 9, 2]
def baseStart_1737139 : Nat := 118140960795 + 1737139 * 2 ^ 59
def prefixEnd_1737139 : Nat := 4983230072969 + 3 ^ 40 * 1737139 * 2
def baseEnd_1737139 : Nat := 891987270670784169373549

theorem tailTrace_1737139 : CollatzResearch.WordTrace tailWord_1737139 prefixEnd_1737139 891987270670784169373549 := by
  unfold tailWord_1737139
  simp only [CollatzResearch.WordTrace]
  refine ⟨63358664453649557566430471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42239109635766371710953647 63358664453649557566430471)
  ·
    refine ⟨95037996680474336349645707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63358664453649557566430471 95037996680474336349645707)
    ·
      refine ⟨142556995020711504524468561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95037996680474336349645707 142556995020711504524468561)
      ·
        refine ⟨106917746265533628393351421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142556995020711504524468561 106917746265533628393351421)
        ·
          refine ⟨40094154849575110647506783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106917746265533628393351421 40094154849575110647506783)
          ·
            refine ⟨60141232274362665971260175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40094154849575110647506783 60141232274362665971260175)
            ·
              refine ⟨90211848411543998956890263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60141232274362665971260175 90211848411543998956890263)
              ·
                refine ⟨135317772617315998435335395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90211848411543998956890263 135317772617315998435335395)
                ·
                  refine ⟨202976658925973997653003093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135317772617315998435335395 202976658925973997653003093)
                  ·
                    refine ⟨1189316360894378892498065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202976658925973997653003093 1189316360894378892498065)
                    ·
                      refine ⟨891987270670784169373549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189316360894378892498065 891987270670784169373549)
                      ·
                        rfl

theorem cell23_1737139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9, 2].length) (baseStart_1737139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737139 prefixEnd_1737139 := by exact prefixLift 1737139
  have htrace : WordTrace (prefixWord ++ tailWord_1737139) baseStart_1737139 baseEnd_1737139 := by
    simpa [prefixWord, tailWord_1737139, baseEnd_1737139] using wordTrace_append hprefix tailTrace_1737139
  have hstable : (prefixWord ++ tailWord_1737139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737139).length < 2 ^ (prefixWord ++ tailWord_1737139).sum := by decide
  have hdescent : baseEnd_1737139 < baseStart_1737139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737152 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1737152 : Nat := 118140960795 + 1737152 * 2 ^ 59
def prefixEnd_1737152 : Nat := 4983230072969 + 3 ^ 40 * 1737152 * 2
def baseEnd_1737152 : Nat := 891993945919292618510989

theorem tailTrace_1737152 : CollatzResearch.WordTrace tailWord_1737152 prefixEnd_1737152 891993945919292618510989 := by
  unfold tailWord_1737152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31679569301301230393326855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42239425735068307191102473 31679569301301230393326855)
  ·
    refine ⟨47519353951951845589990283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31679569301301230393326855 47519353951951845589990283)
    ·
      refine ⟨71279030927927768384985425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47519353951951845589990283 71279030927927768384985425)
      ·
        refine ⟨53459273195945826288739069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71279030927927768384985425 53459273195945826288739069)
        ·
          refine ⟨20047227448479684858277151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53459273195945826288739069 20047227448479684858277151)
          ·
            refine ⟨30070841172719527287415727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20047227448479684858277151 30070841172719527287415727)
            ·
              refine ⟨45106261759079290931123591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30070841172719527287415727 45106261759079290931123591)
              ·
                refine ⟨67659392638618936396685387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45106261759079290931123591 67659392638618936396685387)
                ·
                  refine ⟨101489088957928404595028081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67659392638618936396685387 101489088957928404595028081)
                  ·
                    refine ⟨76116816718446303446271061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101489088957928404595028081 76116816718446303446271061)
                    ·
                      refine ⟨891993945919292618510989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 76116816718446303446271061 891993945919292618510989)
                      ·
                        rfl

theorem cell23_1737152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1737152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737152 prefixEnd_1737152 := by exact prefixLift 1737152
  have htrace : WordTrace (prefixWord ++ tailWord_1737152) baseStart_1737152 baseEnd_1737152 := by
    simpa [prefixWord, tailWord_1737152, baseEnd_1737152] using wordTrace_append hprefix tailTrace_1737152
  have hstable : (prefixWord ++ tailWord_1737152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737152).length < 2 ^ (prefixWord ++ tailWord_1737152).sum := by decide
  have hdescent : baseEnd_1737152 < baseStart_1737152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737203 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 2, 2, 2]
def baseStart_1737203 : Nat := 118140960795 + 1737203 * 2 ^ 59
def prefixEnd_1737203 : Nat := 4983230072969 + 3 ^ 40 * 1737203 * 2
def baseEnd_1737203 : Nat := 892020133432671918973255

theorem tailTrace_1737203 : CollatzResearch.WordTrace tailWord_1737203 prefixEnd_1737203 892020133432671918973255 := by
  unfold tailWord_1737203
  simp only [CollatzResearch.WordTrace]
  refine ⟨63360998725417696496760263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42240665816945130997840175 63360998725417696496760263)
  ·
    refine ⟨95041498088126544745140395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63360998725417696496760263 95041498088126544745140395)
    ·
      refine ⟨142562247132189817117710593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95041498088126544745140395 142562247132189817117710593)
      ·
        refine ⟨106921685349142362838282945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142562247132189817117710593 106921685349142362838282945)
        ·
          refine ⟨80191264011856772128712209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106921685349142362838282945 80191264011856772128712209)
          ·
            refine ⟨60143448008892579096534157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80191264011856772128712209 60143448008892579096534157)
            ·
              refine ⟨22553793003334717161200309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60143448008892579096534157 22553793003334717161200309)
              ·
                refine ⟨2114418094062629733862529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22553793003334717161200309 2114418094062629733862529)
                ·
                  refine ⟨1585813570546972300396897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114418094062629733862529 1585813570546972300396897)
                  ·
                    refine ⟨1189360177910229225297673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585813570546972300396897 1189360177910229225297673)
                    ·
                      refine ⟨892020133432671918973255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189360177910229225297673 892020133432671918973255)
                      ·
                        rfl

theorem cell23_1737203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2, 2].length) (baseStart_1737203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737203 prefixEnd_1737203 := by exact prefixLift 1737203
  have htrace : WordTrace (prefixWord ++ tailWord_1737203) baseStart_1737203 baseEnd_1737203 := by
    simpa [prefixWord, tailWord_1737203, baseEnd_1737203] using wordTrace_append hprefix tailTrace_1737203
  have hstable : (prefixWord ++ tailWord_1737203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737203).length < 2 ^ (prefixWord ++ tailWord_1737203).sum := by decide
  have hdescent : baseEnd_1737203 < baseStart_1737203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737206 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1737206 : Nat := 118140960795 + 1737206 * 2 ^ 59
def prefixEnd_1737206 : Nat := 4983230072969 + 3 ^ 40 * 1737206 * 2
def baseEnd_1737206 : Nat := 892021673874635407235741

theorem tailTrace_1737206 : CollatzResearch.WordTrace tailWord_1737206 prefixEnd_1737206 892021673874635407235741 := by
  unfold tailWord_1737206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960069259025426750569967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42240738762937885339412981 3960069259025426750569967)
  ·
    refine ⟨5940103888538140125854951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960069259025426750569967 5940103888538140125854951)
    ·
      refine ⟨8910155832807210188782427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940103888538140125854951 8910155832807210188782427)
      ·
        refine ⟨13365233749210815283173641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910155832807210188782427 13365233749210815283173641)
        ·
          refine ⟨10023925311908111462380231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13365233749210815283173641 10023925311908111462380231)
          ·
            refine ⟨15035887967862167193570347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023925311908111462380231 15035887967862167193570347)
            ·
              refine ⟨22553831951793250790355521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15035887967862167193570347 22553831951793250790355521)
              ·
                refine ⟨16915373963844938092766641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22553831951793250790355521 16915373963844938092766641)
                ·
                  refine ⟨12686530472883703569574981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16915373963844938092766641 12686530472883703569574981)
                  ·
                    refine ⟨2378724463665694419295309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12686530472883703569574981 2378724463665694419295309)
                    ·
                      refine ⟨892021673874635407235741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378724463665694419295309 892021673874635407235741)
                      ·
                        rfl

theorem cell23_1737206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1737206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737206 prefixEnd_1737206 := by exact prefixLift 1737206
  have htrace : WordTrace (prefixWord ++ tailWord_1737206) baseStart_1737206 baseEnd_1737206 := by
    simpa [prefixWord, tailWord_1737206, baseEnd_1737206] using wordTrace_append hprefix tailTrace_1737206
  have hstable : (prefixWord ++ tailWord_1737206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737206).length < 2 ^ (prefixWord ++ tailWord_1737206).sum := by decide
  have hdescent : baseEnd_1737206 < baseStart_1737206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737219 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1737219 : Nat := 118140960795 + 1737219 * 2 ^ 59
def prefixEnd_1737219 : Nat := 4983230072969 + 3 ^ 40 * 1737219 * 2
def baseEnd_1737219 : Nat := 892028349123143856373181

theorem tailTrace_1737219 : CollatzResearch.WordTrace tailWord_1737219 prefixEnd_1737219 892028349123143856373181 := by
  unfold tailWord_1737219
  simp only [CollatzResearch.WordTrace]
  refine ⟨63361582293359731229342711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42241054862239820819561807 63361582293359731229342711)
  ·
    refine ⟨95042373440039596844014067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63361582293359731229342711 95042373440039596844014067)
    ·
      refine ⟨142563560160059395266021101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95042373440039596844014067 142563560160059395266021101)
      ·
        refine ⟨53461335060022273224757913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142563560160059395266021101 53461335060022273224757913)
        ·
          refine ⟨40096001295016704918568435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53461335060022273224757913 40096001295016704918568435)
          ·
            refine ⟨60144001942525057377852653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40096001295016704918568435 60144001942525057377852653)
            ·
              refine ⟨22554000728446896516694745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60144001942525057377852653 22554000728446896516694745)
              ·
                refine ⟨16915500546335172387521059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22554000728446896516694745 16915500546335172387521059)
                ·
                  refine ⟨25373250819502758581281589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16915500546335172387521059 25373250819502758581281589)
                  ·
                    refine ⟨2378742264328383616995149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25373250819502758581281589 2378742264328383616995149)
                    ·
                      refine ⟨892028349123143856373181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378742264328383616995149 892028349123143856373181)
                      ·
                        rfl

theorem cell23_1737219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1737219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737219 prefixEnd_1737219 := by exact prefixLift 1737219
  have htrace : WordTrace (prefixWord ++ tailWord_1737219) baseStart_1737219 baseEnd_1737219 := by
    simpa [prefixWord, tailWord_1737219, baseEnd_1737219] using wordTrace_append hprefix tailTrace_1737219
  have hstable : (prefixWord ++ tailWord_1737219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737219).length < 2 ^ (prefixWord ++ tailWord_1737219).sum := by decide
  have hdescent : baseEnd_1737219 < baseStart_1737219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737249 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1737249 : Nat := 118140960795 + 1737249 * 2 ^ 59
def prefixEnd_1737249 : Nat := 4983230072969 + 3 ^ 40 * 1737249 * 2
def baseEnd_1737249 : Nat := 892043753542778738998043

theorem tailTrace_1737249 : CollatzResearch.WordTrace tailWord_1737249 prefixEnd_1737249 892043753542778738998043 := by
  unfold tailWord_1737249
  simp only [CollatzResearch.WordTrace]
  refine ⟨63362676483251046352934801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42241784322167364235289867 63362676483251046352934801)
  ·
    refine ⟨47522007362438284764701101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63362676483251046352934801 47522007362438284764701101)
    ·
      refine ⟨17820752760914356786762913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47522007362438284764701101 17820752760914356786762913)
      ·
        refine ⟨13365564570685767590072185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17820752760914356786762913 13365564570685767590072185)
        ·
          refine ⟨10024173428014325692554139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13365564570685767590072185 10024173428014325692554139)
          ·
            refine ⟨15036260142021488538831209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024173428014325692554139 15036260142021488538831209)
            ·
              refine ⟨11277195106516116404123407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15036260142021488538831209 11277195106516116404123407)
              ·
                refine ⟨16915792659774174606185111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277195106516116404123407 16915792659774174606185111)
                ·
                  refine ⟨25373688989661261909277667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16915792659774174606185111 25373688989661261909277667)
                  ·
                    refine ⟨38060533484491892863916501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25373688989661261909277667 38060533484491892863916501)
                    ·
                      refine ⟨892043753542778738998043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38060533484491892863916501 892043753542778738998043)
                      ·
                        rfl

theorem cell23_1737249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1737249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737249 prefixEnd_1737249 := by exact prefixLift 1737249
  have htrace : WordTrace (prefixWord ++ tailWord_1737249) baseStart_1737249 baseEnd_1737249 := by
    simpa [prefixWord, tailWord_1737249, baseEnd_1737249] using wordTrace_append hprefix tailTrace_1737249
  have hstable : (prefixWord ++ tailWord_1737249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737249).length < 2 ^ (prefixWord ++ tailWord_1737249).sum := by decide
  have hdescent : baseEnd_1737249 < baseStart_1737249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737256 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1737256 : Nat := 118140960795 + 1737256 * 2 ^ 59
def prefixEnd_1737256 : Nat := 4983230072969 + 3 ^ 40 * 1737256 * 2
def baseEnd_1737256 : Nat := 297349115969120070536837

theorem tailTrace_1737256 : CollatzResearch.WordTrace tailWord_1737256 prefixEnd_1737256 297349115969120070536837 := by
  unfold tailWord_1737256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681465897112843274219811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42241954529483791032293081 31681465897112843274219811)
  ·
    refine ⟨47522198845669264911329717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31681465897112843274219811 47522198845669264911329717)
    ·
      refine ⟨4455206141781493585437161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47522198845669264911329717 4455206141781493585437161)
      ·
        refine ⟨3341404606336120189077871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4455206141781493585437161 3341404606336120189077871)
        ·
          refine ⟨5012106909504180283616807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341404606336120189077871 5012106909504180283616807)
          ·
            refine ⟨7518160364256270425425211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012106909504180283616807 7518160364256270425425211)
            ·
              refine ⟨11277240546384405638137817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518160364256270425425211 11277240546384405638137817)
              ·
                refine ⟨8457930409788304228603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11277240546384405638137817 8457930409788304228603363)
                ·
                  refine ⟨12686895614682456342905045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457930409788304228603363 12686895614682456342905045)
                  ·
                    refine ⟨297349115969120070536837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12686895614682456342905045 297349115969120070536837)
                    ·
                      rfl

theorem cell23_1737256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1737256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737256 prefixEnd_1737256 := by exact prefixLift 1737256
  have htrace : WordTrace (prefixWord ++ tailWord_1737256) baseStart_1737256 baseEnd_1737256 := by
    simpa [prefixWord, tailWord_1737256, baseEnd_1737256] using wordTrace_append hprefix tailTrace_1737256
  have hstable : (prefixWord ++ tailWord_1737256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737256).length < 2 ^ (prefixWord ++ tailWord_1737256).sum := by decide
  have hdescent : baseEnd_1737256 < baseStart_1737256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737269 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1737269 : Nat := 118140960795 + 1737269 * 2 ^ 59
def prefixEnd_1737269 : Nat := 4983230072969 + 3 ^ 40 * 1737269 * 2
def baseEnd_1737269 : Nat := 297351341051956220249317

theorem tailTrace_1737269 : CollatzResearch.WordTrace tailWord_1737269 prefixEnd_1737269 297351341051956220249317 := by
  unfold tailWord_1737269
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363405943178589768662861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42242270628785726512441907 63363405943178589768662861)
  ·
    refine ⟨23761277228691971163248573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63363405943178589768662861 23761277228691971163248573)
    ·
      refine ⟨8910478960759489186218215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23761277228691971163248573 8910478960759489186218215)
      ·
        refine ⟨13365718441139233779327323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910478960759489186218215 13365718441139233779327323)
        ·
          refine ⟨20048577661708850668990985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13365718441139233779327323 20048577661708850668990985)
          ·
            refine ⟨15036433246281638001743239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20048577661708850668990985 15036433246281638001743239)
            ·
              refine ⟨22554649869422457002614859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036433246281638001743239 22554649869422457002614859)
              ·
                refine ⟨33831974804133685503922289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22554649869422457002614859 33831974804133685503922289)
                ·
                  refine ⟨25373981103100264127941717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33831974804133685503922289 25373981103100264127941717)
                  ·
                    refine ⟨297351341051956220249317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25373981103100264127941717 297351341051956220249317)
                    ·
                      rfl

theorem cell23_1737269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1737269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737269 prefixEnd_1737269 := by exact prefixLift 1737269
  have htrace : WordTrace (prefixWord ++ tailWord_1737269) baseStart_1737269 baseEnd_1737269 := by
    simpa [prefixWord, tailWord_1737269, baseEnd_1737269] using wordTrace_append hprefix tailTrace_1737269
  have hstable : (prefixWord ++ tailWord_1737269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737269).length < 2 ^ (prefixWord ++ tailWord_1737269).sum := by decide
  have hdescent : baseEnd_1737269 < baseStart_1737269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737276 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1737276 : Nat := 118140960795 + 1737276 * 2 ^ 59
def prefixEnd_1737276 : Nat := 4983230072969 + 3 ^ 40 * 1737276 * 2
def baseEnd_1737276 : Nat := 892057617520450133360419

theorem tailTrace_1737276 : CollatzResearch.WordTrace tailWord_1737276 prefixEnd_1737276 892057617520450133360419 := by
  unfold tailWord_1737276
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681830627076614982083841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42242440836102153309445121 31681830627076614982083841)
  ·
    refine ⟨23761372970307461236562881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31681830627076614982083841 23761372970307461236562881)
    ·
      refine ⟨17821029727730595927422161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23761372970307461236562881 17821029727730595927422161)
      ·
        refine ⟨13365772295797946945566621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17821029727730595927422161 13365772295797946945566621)
        ·
          refine ⟨5012164610924230104587483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13365772295797946945566621 5012164610924230104587483)
          ·
            refine ⟨7518246916386345156881225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012164610924230104587483 7518246916386345156881225)
            ·
              refine ⟨5638685187289758867660919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518246916386345156881225 5638685187289758867660919)
              ·
                refine ⟨8458027780934638301491379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638685187289758867660919 8458027780934638301491379)
                ·
                  refine ⟨12687041671401957452237069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8458027780934638301491379 12687041671401957452237069)
                  ·
                    refine ⟨4757640626775734044588901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12687041671401957452237069 4757640626775734044588901)
                    ·
                      refine ⟨892057617520450133360419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4757640626775734044588901 892057617520450133360419)
                      ·
                        rfl

theorem cell23_1737276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1737276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737276 prefixEnd_1737276 := by exact prefixLift 1737276
  have htrace : WordTrace (prefixWord ++ tailWord_1737276) baseStart_1737276 baseEnd_1737276 := by
    simpa [prefixWord, tailWord_1737276, baseEnd_1737276] using wordTrace_append hprefix tailTrace_1737276
  have hstable : (prefixWord ++ tailWord_1737276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737276).length < 2 ^ (prefixWord ++ tailWord_1737276).sum := by decide
  have hdescent : baseEnd_1737276 < baseStart_1737276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737293 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1737293 : Nat := 118140960795 + 1737293 * 2 ^ 59
def prefixEnd_1737293 : Nat := 4983230072969 + 3 ^ 40 * 1737293 * 2
def baseEnd_1737293 : Nat := 892066346691576566847841

theorem tailTrace_1737293 : CollatzResearch.WordTrace tailWord_1737293 prefixEnd_1737293 892066346691576566847841 := by
  unfold tailWord_1737293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63364281295091641867536533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42242854196727761245024355 63364281295091641867536533)
  ·
    refine ⟨2970200685707420712540775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63364281295091641867536533 2970200685707420712540775)
    ·
      refine ⟨4455301028561131068811163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970200685707420712540775 4455301028561131068811163)
      ·
        refine ⟨6682951542841696603216745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455301028561131068811163 6682951542841696603216745)
        ·
          refine ⟨5012213657131272452412559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6682951542841696603216745 5012213657131272452412559)
          ·
            refine ⟨7518320485696908678618839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012213657131272452412559 7518320485696908678618839)
            ·
              refine ⟨11277480728545363017928259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518320485696908678618839 11277480728545363017928259)
              ·
                refine ⟨16916221092818044526892389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277480728545363017928259 16916221092818044526892389)
                ·
                  refine ⟨3171791454903383348792323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16916221092818044526892389 3171791454903383348792323)
                  ·
                    refine ⟨4757687182355075023188485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3171791454903383348792323 4757687182355075023188485)
                    ·
                      refine ⟨892066346691576566847841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4757687182355075023188485 892066346691576566847841)
                      ·
                        rfl

theorem cell23_1737293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1737293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737293 prefixEnd_1737293 := by exact prefixLift 1737293
  have htrace : WordTrace (prefixWord ++ tailWord_1737293) baseStart_1737293 baseEnd_1737293 := by
    simpa [prefixWord, tailWord_1737293, baseEnd_1737293] using wordTrace_append hprefix tailTrace_1737293
  have hstable : (prefixWord ++ tailWord_1737293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737293).length < 2 ^ (prefixWord ++ tailWord_1737293).sum := by decide
  have hdescent : baseEnd_1737293 < baseStart_1737293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737316 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1737316 : Nat := 118140960795 + 1737316 * 2 ^ 59
def prefixEnd_1737316 : Nat := 4983230072969 + 3 ^ 40 * 1737316 * 2
def baseEnd_1737316 : Nat := 99119795194069997428915

theorem tailTrace_1737316 : CollatzResearch.WordTrace tailWord_1737316 prefixEnd_1737316 99119795194069997428915 := by
  unfold tailWord_1737316
  simp only [CollatzResearch.WordTrace]
  refine ⟨31682560087004158397811901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42243413449338877863749201 31682560087004158397811901)
  ·
    refine ⟨11880960032626559399179463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31682560087004158397811901 11880960032626559399179463)
    ·
      refine ⟨17821440048939839098769195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11880960032626559399179463 17821440048939839098769195)
      ·
        refine ⟨26732160073409758648153793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17821440048939839098769195 26732160073409758648153793)
        ·
          refine ⟨20049120055057318986115345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26732160073409758648153793 20049120055057318986115345)
          ·
            refine ⟨15036840041292989239586509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20049120055057318986115345 15036840041292989239586509)
            ·
              refine ⟨5638815015484870964844941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15036840041292989239586509 5638815015484870964844941)
              ·
                refine ⟨2114555630806826611816853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5638815015484870964844941 2114555630806826611816853)
                ·
                  refine ⟨99119795194069997428915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2114555630806826611816853 99119795194069997428915)
                  ·
                    rfl

theorem cell23_1737316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1737316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737316 prefixEnd_1737316 := by exact prefixLift 1737316
  have htrace : WordTrace (prefixWord ++ tailWord_1737316) baseStart_1737316 baseEnd_1737316 := by
    simpa [prefixWord, tailWord_1737316, baseEnd_1737316] using wordTrace_append hprefix tailTrace_1737316
  have hstable : (prefixWord ++ tailWord_1737316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737316).length < 2 ^ (prefixWord ++ tailWord_1737316).sum := by decide
  have hdescent : baseEnd_1737316 < baseStart_1737316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737330 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1737330 : Nat := 118140960795 + 1737330 * 2 ^ 59
def prefixEnd_1737330 : Nat := 4983230072969 + 3 ^ 40 * 1737330 * 2
def baseEnd_1737330 : Nat := 892085345475792922085171

theorem tailTrace_1737330 : CollatzResearch.WordTrace tailWord_1737330 prefixEnd_1737330 892085345475792922085171 := by
  unfold tailWord_1737330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841407698989399296658361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42243753863971731457755629 15841407698989399296658361)
  ·
    refine ⟨11881055774242049472493771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15841407698989399296658361 11881055774242049472493771)
    ·
      refine ⟨17821583661363074208740657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11881055774242049472493771 17821583661363074208740657)
      ·
        refine ⟨13366187746022305656555493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17821583661363074208740657 13366187746022305656555493)
        ·
          refine ⟨2506160202379182310604155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13366187746022305656555493 2506160202379182310604155)
          ·
            refine ⟨3759240303568773465906233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506160202379182310604155 3759240303568773465906233)
            ·
              refine ⟨2819430227676580099429675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759240303568773465906233 2819430227676580099429675)
              ·
                refine ⟨4229145341514870149144513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819430227676580099429675 4229145341514870149144513)
                ·
                  refine ⟨3171859006136152611858385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229145341514870149144513 3171859006136152611858385)
                  ·
                    refine ⟨2378894254602114458893789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3171859006136152611858385 2378894254602114458893789)
                    ·
                      refine ⟨892085345475792922085171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2378894254602114458893789 892085345475792922085171)
                      ·
                        rfl

theorem cell23_1737330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1737330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737330 prefixEnd_1737330 := by exact prefixLift 1737330
  have htrace : WordTrace (prefixWord ++ tailWord_1737330) baseStart_1737330 baseEnd_1737330 := by
    simpa [prefixWord, tailWord_1737330, baseEnd_1737330] using wordTrace_append hprefix tailTrace_1737330
  have hstable : (prefixWord ++ tailWord_1737330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737330).length < 2 ^ (prefixWord ++ tailWord_1737330).sum := by decide
  have hdescent : baseEnd_1737330 < baseStart_1737330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737339 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_1737339 : Nat := 118140960795 + 1737339 * 2 ^ 59
def prefixEnd_1737339 : Nat := 4983230072969 + 3 ^ 40 * 1737339 * 2
def baseEnd_1737339 : Nat := 892089966801683386872629

theorem tailTrace_1737339 : CollatzResearch.WordTrace tailWord_1737339 prefixEnd_1737339 892089966801683386872629 := by
  unfold tailWord_1737339
  simp only [CollatzResearch.WordTrace]
  refine ⟨63365959052924991723711071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42243972701949994482474047 63365959052924991723711071)
  ·
    refine ⟨95048938579387487585566607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63365959052924991723711071 95048938579387487585566607)
    ·
      refine ⟨142573407869081231378349911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95048938579387487585566607 142573407869081231378349911)
      ·
        refine ⟨213860111803621847067524867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142573407869081231378349911 213860111803621847067524867)
        ·
          refine ⟨320790167705432770601287301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213860111803621847067524867 320790167705432770601287301)
          ·
            refine ⟨60148156444768644487741369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320790167705432770601287301 60148156444768644487741369)
            ·
              refine ⟨45111117333576483365806027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60148156444768644487741369 45111117333576483365806027)
              ·
                refine ⟨67666676000364725048709041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45111117333576483365806027 67666676000364725048709041)
                ·
                  refine ⟨50750007000273543786531781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67666676000364725048709041 50750007000273543786531781)
                  ·
                    refine ⟨9515626312551289459974709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50750007000273543786531781 9515626312551289459974709)
                    ·
                      refine ⟨892089966801683386872629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9515626312551289459974709 892089966801683386872629)
                      ·
                        rfl

theorem cell23_1737339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_1737339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737339 prefixEnd_1737339 := by exact prefixLift 1737339
  have htrace : WordTrace (prefixWord ++ tailWord_1737339) baseStart_1737339 baseEnd_1737339 := by
    simpa [prefixWord, tailWord_1737339, baseEnd_1737339] using wordTrace_append hprefix tailTrace_1737339
  have hstable : (prefixWord ++ tailWord_1737339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737339).length < 2 ^ (prefixWord ++ tailWord_1737339).sum := by decide
  have hdescent : baseEnd_1737339 < baseStart_1737339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737354 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1737354 : Nat := 118140960795 + 1737354 * 2 ^ 59
def prefixEnd_1737354 : Nat := 4983230072969 + 3 ^ 40 * 1737354 * 2
def baseEnd_1737354 : Nat := 297365889670500276061687

theorem tailTrace_1737354 : CollatzResearch.WordTrace tailWord_1737354 prefixEnd_1737354 297365889670500276061687 := by
  unfold tailWord_1737354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841626536967662321376779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42244337431913766190338077 15841626536967662321376779)
  ·
    refine ⟨23762439805451493482065169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15841626536967662321376779 23762439805451493482065169)
    ·
      refine ⟨17821829854088620111548877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23762439805451493482065169 17821829854088620111548877)
      ·
        refine ⟨6683186195283232541830829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17821829854088620111548877 6683186195283232541830829)
        ·
          refine ⟨2506194823231212203186561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6683186195283232541830829 2506194823231212203186561)
          ·
            refine ⟨1879646117423409152389921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2506194823231212203186561 1879646117423409152389921)
            ·
              refine ⟨1409734588067556864292441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879646117423409152389921 1409734588067556864292441)
              ·
                refine ⟨1057300941050667648219331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409734588067556864292441 1057300941050667648219331)
                ·
                  refine ⟨1585951411576001472328997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057300941050667648219331 1585951411576001472328997)
                  ·
                    refine ⟨297365889670500276061687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1585951411576001472328997 297365889670500276061687)
                    ·
                      rfl

theorem cell23_1737354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1737354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737354 prefixEnd_1737354 := by exact prefixLift 1737354
  have htrace : WordTrace (prefixWord ++ tailWord_1737354) baseStart_1737354 baseEnd_1737354 := by
    simpa [prefixWord, tailWord_1737354, baseEnd_1737354] using wordTrace_append hprefix tailTrace_1737354
  have hstable : (prefixWord ++ tailWord_1737354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737354).length < 2 ^ (prefixWord ++ tailWord_1737354).sum := by decide
  have hdescent : baseEnd_1737354 < baseStart_1737354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737397 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1737397 : Nat := 118140960795 + 1737397 * 2 ^ 59
def prefixEnd_1737397 : Nat := 4983230072969 + 3 ^ 40 * 1737397 * 2
def baseEnd_1737397 : Nat := 297373249559881386649121

theorem tailTrace_1737397 : CollatzResearch.WordTrace tailWord_1737397 prefixEnd_1737397 297373249559881386649121 := by
  unfold tailWord_1737397
  simp only [CollatzResearch.WordTrace]
  refine ⟨63368074486714867629322445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42245382991143245086214963 63368074486714867629322445)
  ·
    refine ⟨23763027932518075360995917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63368074486714867629322445 23763027932518075360995917)
    ·
      refine ⟨8911135474694278260373469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23763027932518075360995917 8911135474694278260373469)
      ·
        refine ⟨3341675803010354347640051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8911135474694278260373469 3341675803010354347640051)
        ·
          refine ⟨5012513704515531521460077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341675803010354347640051 5012513704515531521460077)
          ·
            refine ⟨1879692639193324320547529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5012513704515531521460077 1879692639193324320547529)
            ·
              refine ⟨1409769479394993240410647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879692639193324320547529 1409769479394993240410647)
              ·
                refine ⟨2114654219092489860615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409769479394993240410647 2114654219092489860615971)
                ·
                  refine ⟨3171981328638734790923957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114654219092489860615971 3171981328638734790923957)
                  ·
                    refine ⟨297373249559881386649121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3171981328638734790923957 297373249559881386649121)
                    ·
                      rfl

theorem cell23_1737397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1737397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737397 prefixEnd_1737397 := by exact prefixLift 1737397
  have htrace : WordTrace (prefixWord ++ tailWord_1737397) baseStart_1737397 baseEnd_1737397 := by
    simpa [prefixWord, tailWord_1737397, baseEnd_1737397] using wordTrace_append hprefix tailTrace_1737397
  have hstable : (prefixWord ++ tailWord_1737397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737397).length < 2 ^ (prefixWord ++ tailWord_1737397).sum := by decide
  have hdescent : baseEnd_1737397 < baseStart_1737397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737406 : List Nat := [4, 2, 1, 1, 2, 1, 12]
def baseStart_1737406 : Nat := 118140960795 + 1737406 * 2 ^ 59
def prefixEnd_1737406 : Nat := 4983230072969 + 3 ^ 40 * 1737406 * 2
def baseEnd_1737406 : Nat := 11013881111179439811541

theorem tailTrace_1737406 : CollatzResearch.WordTrace tailWord_1737406 prefixEnd_1737406 11013881111179439811541 := by
  unfold tailWord_1737406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921050342960282770800009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42245601829121508110933381 7921050342960282770800009)
  ·
    refine ⟨5940787757220212078100007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7921050342960282770800009 5940787757220212078100007)
    ·
      refine ⟨8911181635830318117150011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940787757220212078100007 8911181635830318117150011)
      ·
        refine ⟨13366772453745477175725017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8911181635830318117150011 13366772453745477175725017)
        ·
          refine ⟨10025079340309107881793763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13366772453745477175725017 10025079340309107881793763)
          ·
            refine ⟨15037619010463661822690645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10025079340309107881793763 15037619010463661822690645)
            ·
              refine ⟨11013881111179439811541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15037619010463661822690645 11013881111179439811541)
              ·
                rfl

theorem cell23_1737406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 12].length) (baseStart_1737406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737406 prefixEnd_1737406 := by exact prefixLift 1737406
  have htrace : WordTrace (prefixWord ++ tailWord_1737406) baseStart_1737406 baseEnd_1737406 := by
    simpa [prefixWord, tailWord_1737406, baseEnd_1737406] using wordTrace_append hprefix tailTrace_1737406
  have hstable : (prefixWord ++ tailWord_1737406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737406).length < 2 ^ (prefixWord ++ tailWord_1737406).sum := by decide
  have hdescent : baseEnd_1737406 < baseStart_1737406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737466 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1737466 : Nat := 118140960795 + 1737466 * 2 ^ 59
def prefixEnd_1737466 : Nat := 4983230072969 + 3 ^ 40 * 1737466 * 2
def baseEnd_1737466 : Nat := 297385059614934796661515

theorem tailTrace_1737466 : CollatzResearch.WordTrace tailWord_1737466 prefixEnd_1737466 297385059614934796661515 := by
  unfold tailWord_1737466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842647780866223103396063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42247060748976594942389501 15842647780866223103396063)
  ·
    refine ⟨23763971671299334655094095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15842647780866223103396063 23763971671299334655094095)
    ·
      refine ⟨35645957506949001982641143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23763971671299334655094095 35645957506949001982641143)
      ·
        refine ⟨53468936260423502973961715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35645957506949001982641143 53468936260423502973961715)
        ·
          refine ⟨80203404390635254460942573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53468936260423502973961715 80203404390635254460942573)
          ·
            refine ⟨30076276646488220422853465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80203404390635254460942573 30076276646488220422853465)
            ·
              refine ⟨22557207484866165317140099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30076276646488220422853465 22557207484866165317140099)
              ·
                refine ⟨33835811227299247975710149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22557207484866165317140099 33835811227299247975710149)
                ·
                  refine ⟨6344214605118608995445653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33835811227299247975710149 6344214605118608995445653)
                  ·
                    refine ⟨297385059614934796661515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6344214605118608995445653 297385059614934796661515)
                    ·
                      rfl

theorem cell23_1737466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1737466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737466 prefixEnd_1737466 := by exact prefixLift 1737466
  have htrace : WordTrace (prefixWord ++ tailWord_1737466) baseStart_1737466 baseEnd_1737466 := by
    simpa [prefixWord, tailWord_1737466, baseEnd_1737466] using wordTrace_append hprefix tailTrace_1737466
  have hstable : (prefixWord ++ tailWord_1737466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737466).length < 2 ^ (prefixWord ++ tailWord_1737466).sum := by decide
  have hdescent : baseEnd_1737466 < baseStart_1737466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737496 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 9]
def baseStart_1737496 : Nat := 118140960795 + 1737496 * 2 ^ 59
def prefixEnd_1737496 : Nat := 4983230072969 + 3 ^ 40 * 1737496 * 2
def baseEnd_1737496 : Nat := 99130064807159919178823

theorem tailTrace_1737496 : CollatzResearch.WordTrace tailWord_1737496 prefixEnd_1737496 99130064807159919178823 := by
  unfold tailWord_1737496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31685842656678103768588171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42247790208904138358117561 31685842656678103768588171)
  ·
    refine ⟨47528763985017155652882257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31685842656678103768588171 47528763985017155652882257)
    ·
      refine ⟨35646572988762866739661693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47528763985017155652882257 35646572988762866739661693)
      ·
        refine ⟨13367464870786075027373135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35646572988762866739661693 13367464870786075027373135)
        ·
          refine ⟨20051197306179112541059703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367464870786075027373135 20051197306179112541059703)
          ·
            refine ⟨30076795959268668811589555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20051197306179112541059703 30076795959268668811589555)
            ·
              refine ⟨45115193938903003217384333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30076795959268668811589555 45115193938903003217384333)
              ·
                refine ⟨16918197727088626206519125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45115193938903003217384333 16918197727088626206519125)
                ·
                  refine ⟨99130064807159919178823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16918197727088626206519125 99130064807159919178823)
                  ·
                    rfl

theorem cell23_1737496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_1737496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737496 prefixEnd_1737496 := by exact prefixLift 1737496
  have htrace : WordTrace (prefixWord ++ tailWord_1737496) baseStart_1737496 baseEnd_1737496 := by
    simpa [prefixWord, tailWord_1737496, baseEnd_1737496] using wordTrace_append hprefix tailTrace_1737496
  have hstable : (prefixWord ++ tailWord_1737496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737496).length < 2 ^ (prefixWord ++ tailWord_1737496).sum := by decide
  have hdescent : baseEnd_1737496 < baseStart_1737496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737537 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1737537 : Nat := 118140960795 + 1737537 * 2 ^ 59
def prefixEnd_1737537 : Nat := 4983230072969 + 3 ^ 40 * 1737537 * 2
def baseEnd_1737537 : Nat := 892191635971273612196719

theorem tailTrace_1737537 : CollatzResearch.WordTrace tailWord_1737537 prefixEnd_1737537 892191635971273612196719 := by
  unfold tailWord_1737537
  simp only [CollatzResearch.WordTrace]
  refine ⟨63373180706207671539418865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42248787137471781026279243 63373180706207671539418865)
  ·
    refine ⟨47529885529655753654564149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63373180706207671539418865 47529885529655753654564149)
    ·
      refine ⟨4455926768405226905115389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47529885529655753654564149 4455926768405226905115389)
      ·
        refine ⟨1670972538151960089418271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4455926768405226905115389 1670972538151960089418271)
        ·
          refine ⟨2506458807227940134127407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670972538151960089418271 2506458807227940134127407)
          ·
            refine ⟨3759688210841910201191111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506458807227940134127407 3759688210841910201191111)
            ·
              refine ⟨5639532316262865301786667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759688210841910201191111 5639532316262865301786667)
              ·
                refine ⟨8459298474394297952680001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639532316262865301786667 8459298474394297952680001)
                ·
                  refine ⟨6344473855795723464510001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8459298474394297952680001 6344473855795723464510001)
                  ·
                    refine ⟨4758355391846792598382501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344473855795723464510001 4758355391846792598382501)
                    ·
                      refine ⟨892191635971273612196719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4758355391846792598382501 892191635971273612196719)
                      ·
                        rfl

theorem cell23_1737537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1737537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737537 prefixEnd_1737537 := by exact prefixLift 1737537
  have htrace : WordTrace (prefixWord ++ tailWord_1737537) baseStart_1737537 baseEnd_1737537 := by
    simpa [prefixWord, tailWord_1737537, baseEnd_1737537] using wordTrace_append hprefix tailTrace_1737537
  have hstable : (prefixWord ++ tailWord_1737537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737537).length < 2 ^ (prefixWord ++ tailWord_1737537).sum := by decide
  have hdescent : baseEnd_1737537 < baseStart_1737537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737580 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_1737580 : Nat := 118140960795 + 1737580 * 2 ^ 59
def prefixEnd_1737580 : Nat := 4983230072969 + 3 ^ 40 * 1737580 * 2
def baseEnd_1737580 : Nat := 892213715639416943959021

theorem tailTrace_1737580 : CollatzResearch.WordTrace tailWord_1737580 prefixEnd_1737580 892213715639416943959021 := by
  unfold tailWord_1737580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687374522525944941617097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42249832696701259922156129 31687374522525944941617097)
  ·
    refine ⟨23765530891894458706212823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31687374522525944941617097 23765530891894458706212823)
    ·
      refine ⟨35648296337841688059319235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23765530891894458706212823 35648296337841688059319235)
      ·
        refine ⟨53472444506762532088978853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35648296337841688059319235 53472444506762532088978853)
        ·
          refine ⟨10026083345017974766683535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53472444506762532088978853 10026083345017974766683535)
          ·
            refine ⟨15039125017526962150025303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026083345017974766683535 15039125017526962150025303)
            ·
              refine ⟨22558687526290443225037955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15039125017526962150025303 22558687526290443225037955)
              ·
                refine ⟨33838031289435664837556933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558687526290443225037955 33838031289435664837556933)
                ·
                  refine ⟨6344630866769187157041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33838031289435664837556933 6344630866769187157041925)
                  ·
                    refine ⟨1189618287519222591945361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344630866769187157041925 1189618287519222591945361)
                    ·
                      refine ⟨892213715639416943959021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189618287519222591945361 892213715639416943959021)
                      ·
                        rfl

theorem cell23_1737580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_1737580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737580 prefixEnd_1737580 := by exact prefixLift 1737580
  have htrace : WordTrace (prefixWord ++ tailWord_1737580) baseStart_1737580 baseEnd_1737580 := by
    simpa [prefixWord, tailWord_1737580, baseEnd_1737580] using wordTrace_append hprefix tailTrace_1737580
  have hstable : (prefixWord ++ tailWord_1737580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737580).length < 2 ^ (prefixWord ++ tailWord_1737580).sum := by decide
  have hdescent : baseEnd_1737580 < baseStart_1737580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737684 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1737684 : Nat := 118140960795 + 1737684 * 2 ^ 59
def prefixEnd_1737684 : Nat := 4983230072969 + 3 ^ 40 * 1737684 * 2
def baseEnd_1737684 : Nat := 297422372542494845686181

theorem tailTrace_1737684 : CollatzResearch.WordTrace tailWord_1737684 prefixEnd_1737684 297422372542494845686181 := by
  unfold tailWord_1737684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31689271118337557822510053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42252361491116743763346737 31689271118337557822510053)
  ·
    refine ⟨5941738334688292091720635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31689271118337557822510053 5941738334688292091720635)
    ·
      refine ⟨8912607502032438137580953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5941738334688292091720635 8912607502032438137580953)
      ·
        refine ⟨6684455626524328603185715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912607502032438137580953 6684455626524328603185715)
        ·
          refine ⟨10026683439786492904778573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684455626524328603185715 10026683439786492904778573)
          ·
            refine ⟨3760006289919934839291965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10026683439786492904778573 3760006289919934839291965)
            ·
              refine ⟨1410002358719975564734487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3760006289919934839291965 1410002358719975564734487)
              ·
                refine ⟨2115003538079963347101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410002358719975564734487 2115003538079963347101731)
                ·
                  refine ⟨3172505307119945020652597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115003538079963347101731 3172505307119945020652597)
                  ·
                    refine ⟨297422372542494845686181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3172505307119945020652597 297422372542494845686181)
                    ·
                      rfl

theorem cell23_1737684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1737684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737684 prefixEnd_1737684 := by exact prefixLift 1737684
  have htrace : WordTrace (prefixWord ++ tailWord_1737684) baseStart_1737684 baseEnd_1737684 := by
    simpa [prefixWord, tailWord_1737684, baseEnd_1737684] using wordTrace_append hprefix tailTrace_1737684
  have hstable : (prefixWord ++ tailWord_1737684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737684).length < 2 ^ (prefixWord ++ tailWord_1737684).sum := by decide
  have hdescent : baseEnd_1737684 < baseStart_1737684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737687 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_1737687 : Nat := 118140960795 + 1737687 * 2 ^ 59
def prefixEnd_1737687 : Nat := 4983230072969 + 3 ^ 40 * 1737687 * 2
def baseEnd_1737687 : Nat := 892268658069448025321029

theorem tailTrace_1737687 : CollatzResearch.WordTrace tailWord_1737687 prefixEnd_1737687 892268658069448025321029 := by
  unfold tailWord_1737687
  simp only [CollatzResearch.WordTrace]
  refine ⟨63378651655664247157379315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42252434437109498104919543 63378651655664247157379315)
  ·
    refine ⟨95067977483496370736068973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63378651655664247157379315 95067977483496370736068973)
    ·
      refine ⟨35650491556311139026025865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95067977483496370736068973 35650491556311139026025865)
      ·
        refine ⟨26737868667233354269519399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35650491556311139026025865 26737868667233354269519399)
        ·
          refine ⟨40106803000850031404279099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26737868667233354269519399 40106803000850031404279099)
          ·
            refine ⟨60160204501275047106418649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40106803000850031404279099 60160204501275047106418649)
            ·
              refine ⟨45120153375956285329813987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60160204501275047106418649 45120153375956285329813987)
              ·
                refine ⟨67680230063934427994720981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45120153375956285329813987 67680230063934427994720981)
                ·
                  refine ⟨1586255392123463156126273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 67680230063934427994720981 1586255392123463156126273)
                  ·
                    refine ⟨1189691544092597367094705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586255392123463156126273 1189691544092597367094705)
                    ·
                      refine ⟨892268658069448025321029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189691544092597367094705 892268658069448025321029)
                      ·
                        rfl

theorem cell23_1737687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_1737687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737687 prefixEnd_1737687 := by exact prefixLift 1737687
  have htrace : WordTrace (prefixWord ++ tailWord_1737687) baseStart_1737687 baseEnd_1737687 := by
    simpa [prefixWord, tailWord_1737687, baseEnd_1737687] using wordTrace_append hprefix tailTrace_1737687
  have hstable : (prefixWord ++ tailWord_1737687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737687).length < 2 ^ (prefixWord ++ tailWord_1737687).sum := by decide
  have hdescent : baseEnd_1737687 < baseStart_1737687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737698 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1737698 : Nat := 118140960795 + 1737698 * 2 ^ 59
def prefixEnd_1737698 : Nat := 4983230072969 + 3 ^ 40 * 1737698 * 2
def baseEnd_1737698 : Nat := 892274306356647482283479

theorem tailTrace_1737698 : CollatzResearch.WordTrace tailWord_1737698 prefixEnd_1737698 892274306356647482283479 := by
  unfold tailWord_1737698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844763214656099009007437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42252701905749597357353165 15844763214656099009007437)
  ·
    refine ⟨5941786205496037128377789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15844763214656099009007437 5941786205496037128377789)
    ·
      refine ⟨2228169827061013923141671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5941786205496037128377789 2228169827061013923141671)
      ·
        refine ⟨3342254740591520884712507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228169827061013923141671 3342254740591520884712507)
        ·
          refine ⟨5013382110887281327068761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342254740591520884712507 5013382110887281327068761)
          ·
            refine ⟨3760036583165460995301571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013382110887281327068761 3760036583165460995301571)
            ·
              refine ⟨5640054874748191492952357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760036583165460995301571 5640054874748191492952357)
              ·
                refine ⟨1057510289015285904928567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5640054874748191492952357 1057510289015285904928567)
                ·
                  refine ⟨1586265433522928857392851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057510289015285904928567 1586265433522928857392851)
                  ·
                    refine ⟨2379398150284393286089277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586265433522928857392851 2379398150284393286089277)
                    ·
                      refine ⟨892274306356647482283479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2379398150284393286089277 892274306356647482283479)
                      ·
                        rfl

theorem cell23_1737698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1737698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737698 prefixEnd_1737698 := by exact prefixLift 1737698
  have htrace : WordTrace (prefixWord ++ tailWord_1737698) baseStart_1737698 baseEnd_1737698 := by
    simpa [prefixWord, tailWord_1737698, baseEnd_1737698] using wordTrace_append hprefix tailTrace_1737698
  have hstable : (prefixWord ++ tailWord_1737698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737698).length < 2 ^ (prefixWord ++ tailWord_1737698).sum := by decide
  have hdescent : baseEnd_1737698 < baseStart_1737698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737714 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_1737714 : Nat := 118140960795 + 1737714 * 2 ^ 59
def prefixEnd_1737714 : Nat := 4983230072969 + 3 ^ 40 * 1737714 * 2
def baseEnd_1737714 : Nat := 297427507349039806561135

theorem tailTrace_1737714 : CollatzResearch.WordTrace tailWord_1737714 prefixEnd_1737714 297427507349039806561135 := by
  unfold tailWord_1737714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844909106641607692153049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42253090951044287179074797 15844909106641607692153049)
  ·
    refine ⟨11883681829981205769114787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15844909106641607692153049 11883681829981205769114787)
    ·
      refine ⟨17825522744971808653672181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11883681829981205769114787 17825522744971808653672181)
      ·
        refine ⟨1671142757341107061281767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17825522744971808653672181 1671142757341107061281767)
        ·
          refine ⟨2506714136011660591922651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671142757341107061281767 2506714136011660591922651)
          ·
            refine ⟨3760071204017490887883977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506714136011660591922651 3760071204017490887883977)
            ·
              refine ⟨2820053403013118165912983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760071204017490887883977 2820053403013118165912983)
              ·
                refine ⟨4230080104519677248869475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820053403013118165912983 4230080104519677248869475)
                ·
                  refine ⟨6345120156779515873304213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230080104519677248869475 6345120156779515873304213)
                  ·
                    refine ⟨297427507349039806561135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6345120156779515873304213 297427507349039806561135)
                    ·
                      rfl

theorem cell23_1737714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_1737714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737714 prefixEnd_1737714 := by exact prefixLift 1737714
  have htrace : WordTrace (prefixWord ++ tailWord_1737714) baseStart_1737714 baseEnd_1737714 := by
    simpa [prefixWord, tailWord_1737714, baseEnd_1737714] using wordTrace_append hprefix tailTrace_1737714
  have hstable : (prefixWord ++ tailWord_1737714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737714).length < 2 ^ (prefixWord ++ tailWord_1737714).sum := by decide
  have hdescent : baseEnd_1737714 < baseStart_1737714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737723 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 7]
def baseStart_1737723 : Nat := 118140960795 + 1737723 * 2 ^ 59
def prefixEnd_1737723 : Nat := 4983230072969 + 3 ^ 40 * 1737723 * 2
def baseEnd_1737723 : Nat := 297429047791003294823621

theorem tailTrace_1737723 : CollatzResearch.WordTrace tailWord_1737723 prefixEnd_1737723 297429047791003294823621 := by
  unfold tailWord_1737723
  simp only [CollatzResearch.WordTrace]
  refine ⟨63379964683533825305689823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42253309789022550203793215 63379964683533825305689823)
  ·
    refine ⟨95069947025300737958534735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63379964683533825305689823 95069947025300737958534735)
    ·
      refine ⟨142604920537951106937802103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95069947025300737958534735 142604920537951106937802103)
      ·
        refine ⟨213907380806926660406703155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142604920537951106937802103 213907380806926660406703155)
        ·
          refine ⟨320861071210389990610054733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213907380806926660406703155 320861071210389990610054733)
          ·
            refine ⟨120322901703896246478770525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320861071210389990610054733 120322901703896246478770525)
            ·
              refine ⟨45121088138961092429538947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120322901703896246478770525 45121088138961092429538947)
              ·
                refine ⟨67681632208441638644308421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45121088138961092429538947 67681632208441638644308421)
                ·
                  refine ⟨12690306039082807245807829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67681632208441638644308421 12690306039082807245807829)
                  ·
                    refine ⟨297429047791003294823621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12690306039082807245807829 297429047791003294823621)
                    ·
                      rfl

theorem cell23_1737723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_1737723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737723 prefixEnd_1737723 := by exact prefixLift 1737723
  have htrace : WordTrace (prefixWord ++ tailWord_1737723) baseStart_1737723 baseEnd_1737723 := by
    simpa [prefixWord, tailWord_1737723, baseEnd_1737723] using wordTrace_append hprefix tailTrace_1737723
  have hstable : (prefixWord ++ tailWord_1737723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737723).length < 2 ^ (prefixWord ++ tailWord_1737723).sum := by decide
  have hdescent : baseEnd_1737723 < baseStart_1737723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737738 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_1737738 : Nat := 118140960795 + 1737738 * 2 ^ 59
def prefixEnd_1737738 : Nat := 4983230072969 + 3 ^ 40 * 1737738 * 2
def baseEnd_1737738 : Nat := 892294845582827325783295

theorem tailTrace_1737738 : CollatzResearch.WordTrace tailWord_1737738 prefixEnd_1737738 892294845582827325783295 := by
  unfold tailWord_1737738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845127944619870716871467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42253674518986321911657245 15845127944619870716871467)
  ·
    refine ⟨23767691916929806075307201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15845127944619870716871467 23767691916929806075307201)
    ·
      refine ⟨17825768937697354556480401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23767691916929806075307201 17825768937697354556480401)
      ·
        refine ⟨13369326703273015917360301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17825768937697354556480401 13369326703273015917360301)
        ·
          refine ⟨5013497513727380969010113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13369326703273015917360301 5013497513727380969010113)
          ·
            refine ⟨3760123135295535726757585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013497513727380969010113 3760123135295535726757585)
            ·
              refine ⟨2820092351471651795068189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760123135295535726757585 2820092351471651795068189)
              ·
                refine ⟨1057534631801869423150571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820092351471651795068189 1057534631801869423150571)
                ·
                  refine ⟨1586301947702804134725857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057534631801869423150571 1586301947702804134725857)
                  ·
                    refine ⟨1189726460777103101044393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586301947702804134725857 1189726460777103101044393)
                    ·
                      refine ⟨892294845582827325783295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189726460777103101044393 892294845582827325783295)
                      ·
                        rfl

theorem cell23_1737738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_1737738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737738 prefixEnd_1737738 := by exact prefixLift 1737738
  have htrace : WordTrace (prefixWord ++ tailWord_1737738) baseStart_1737738 baseEnd_1737738 := by
    simpa [prefixWord, tailWord_1737738, baseEnd_1737738] using wordTrace_append hprefix tailTrace_1737738
  have hstable : (prefixWord ++ tailWord_1737738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737738).length < 2 ^ (prefixWord ++ tailWord_1737738).sum := by decide
  have hdescent : baseEnd_1737738 < baseStart_1737738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737743 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_1737743 : Nat := 118140960795 + 1737743 * 2 ^ 59
def prefixEnd_1737743 : Nat := 4983230072969 + 3 ^ 40 * 1737743 * 2
def baseEnd_1737743 : Nat := 892297412986099806220771

theorem tailTrace_1737743 : CollatzResearch.WordTrace tailWord_1737743 prefixEnd_1737743 892297412986099806220771 := by
  unfold tailWord_1737743
  simp only [CollatzResearch.WordTrace]
  refine ⟨63380694143461368721417883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42253796095640912480945255 63380694143461368721417883)
  ·
    refine ⟨95071041215192053082126825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63380694143461368721417883 95071041215192053082126825)
    ·
      refine ⟨71303280911394039811595119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95071041215192053082126825 71303280911394039811595119)
      ·
        refine ⟨106954921367091059717392679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71303280911394039811595119 106954921367091059717392679)
        ·
          refine ⟨160432382050636589576089019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106954921367091059717392679 160432382050636589576089019)
          ·
            refine ⟨240648573075954884364133529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160432382050636589576089019 240648573075954884364133529)
            ·
              refine ⟨180486429806966163273100147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240648573075954884364133529 180486429806966163273100147)
              ·
                refine ⟨270729644710449244909650221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180486429806966163273100147 270729644710449244909650221)
                ·
                  refine ⟨101523616766418466841118833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270729644710449244909650221 101523616766418466841118833)
                  ·
                    refine ⟨76142712574813850130839125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101523616766418466841118833 76142712574813850130839125)
                    ·
                      refine ⟨892297412986099806220771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 76142712574813850130839125 892297412986099806220771)
                      ·
                        rfl

theorem cell23_1737743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_1737743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737743 prefixEnd_1737743 := by exact prefixLift 1737743
  have htrace : WordTrace (prefixWord ++ tailWord_1737743) baseStart_1737743 baseEnd_1737743 := by
    simpa [prefixWord, tailWord_1737743, baseEnd_1737743] using wordTrace_append hprefix tailTrace_1737743
  have hstable : (prefixWord ++ tailWord_1737743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737743).length < 2 ^ (prefixWord ++ tailWord_1737743).sum := by decide
  have hdescent : baseEnd_1737743 < baseStart_1737743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737798 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1737798 : Nat := 118140960795 + 1737798 * 2 ^ 59
def prefixEnd_1737798 : Nat := 4983230072969 + 3 ^ 40 * 1737798 * 2
def baseEnd_1737798 : Nat := 892325654422097091033019

theorem tailTrace_1737798 : CollatzResearch.WordTrace tailWord_1737798 prefixEnd_1737798 892325654422097091033019 := by
  unfold tailWord_1737798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980709379945691034833439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42255133438841408743113365 1980709379945691034833439)
  ·
    refine ⟨2971064069918536552250159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980709379945691034833439 2971064069918536552250159)
    ·
      refine ⟨4456596104877804828375239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971064069918536552250159 4456596104877804828375239)
      ·
        refine ⟨6684894157316707242562859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456596104877804828375239 6684894157316707242562859)
        ·
          refine ⟨10027341235975060863844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684894157316707242562859 10027341235975060863844289)
          ·
            refine ⟨7520505926981295647883217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10027341235975060863844289 7520505926981295647883217)
            ·
              refine ⟨5640379445235971735912413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520505926981295647883217 5640379445235971735912413)
              ·
                refine ⟨2115142291963489400967155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5640379445235971735912413 2115142291963489400967155)
                ·
                  refine ⟨3172713437945234101450733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115142291963489400967155 3172713437945234101450733)
                  ·
                    refine ⟨1189767539229462788044025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172713437945234101450733 1189767539229462788044025)
                    ·
                      refine ⟨892325654422097091033019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189767539229462788044025 892325654422097091033019)
                      ·
                        rfl

theorem cell23_1737798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1737798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737798 prefixEnd_1737798 := by exact prefixLift 1737798
  have htrace : WordTrace (prefixWord ++ tailWord_1737798) baseStart_1737798 baseEnd_1737798 := by
    simpa [prefixWord, tailWord_1737798, baseEnd_1737798] using wordTrace_append hprefix tailTrace_1737798
  have hstable : (prefixWord ++ tailWord_1737798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737798).length < 2 ^ (prefixWord ++ tailWord_1737798).sum := by decide
  have hdescent : baseEnd_1737798 < baseStart_1737798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737822 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1737822 : Nat := 118140960795 + 1737822 * 2 ^ 59
def prefixEnd_1737822 : Nat := 4983230072969 + 3 ^ 40 * 1737822 * 2
def baseEnd_1737822 : Nat := 892337977957804997132909

theorem tailTrace_1737822 : CollatzResearch.WordTrace tailWord_1737822 prefixEnd_1737822 892337977957804997132909 := by
  unfold tailWord_1737822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922946938771895651692965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42255717006783443475695813 7922946938771895651692965)
  ·
    refine ⟨1485552551019730434692431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7922946938771895651692965 1485552551019730434692431)
    ·
      refine ⟨2228328826529595652038647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485552551019730434692431 2228328826529595652038647)
      ·
        refine ⟨3342493239794393478057971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228328826529595652038647 3342493239794393478057971)
        ·
          refine ⟨5013739859691590217086957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342493239794393478057971 5013739859691590217086957)
          ·
            refine ⟨1880152447384346331407609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5013739859691590217086957 1880152447384346331407609)
            ·
              refine ⟨1410114335538259748555707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880152447384346331407609 1410114335538259748555707)
              ·
                refine ⟨2115171503307389622833561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410114335538259748555707 2115171503307389622833561)
                ·
                  refine ⟨1586378627480542217125171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2115171503307389622833561 1586378627480542217125171)
                  ·
                    refine ⟨2379567941220813325687757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586378627480542217125171 2379567941220813325687757)
                    ·
                      refine ⟨892337977957804997132909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2379567941220813325687757 892337977957804997132909)
                      ·
                        rfl

theorem cell23_1737822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1737822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737822 prefixEnd_1737822 := by exact prefixLift 1737822
  have htrace : WordTrace (prefixWord ++ tailWord_1737822) baseStart_1737822 baseEnd_1737822 := by
    simpa [prefixWord, tailWord_1737822, baseEnd_1737822] using wordTrace_append hprefix tailTrace_1737822
  have hstable : (prefixWord ++ tailWord_1737822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737822).length < 2 ^ (prefixWord ++ tailWord_1737822).sum := by decide
  have hdescent : baseEnd_1737822 < baseStart_1737822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737840 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1737840 : Nat := 118140960795 + 1737840 * 2 ^ 59
def prefixEnd_1737840 : Nat := 4983230072969 + 3 ^ 40 * 1737840 * 2
def baseEnd_1737840 : Nat := 892347220609585926707825

theorem tailTrace_1737840 : CollatzResearch.WordTrace tailWord_1737840 prefixEnd_1737840 892347220609585926707825 := by
  unfold tailWord_1737840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692116012054977143849487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42256154682739969525132649 31692116012054977143849487)
  ·
    refine ⟨47538174018082465715774231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31692116012054977143849487 47538174018082465715774231)
    ·
      refine ⟨71307261027123698573661347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47538174018082465715774231 71307261027123698573661347)
      ·
        refine ⟨106960891540685547860492021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71307261027123698573661347 106960891540685547860492021)
        ·
          refine ⟨10027583581939270111921127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106960891540685547860492021 10027583581939270111921127)
          ·
            refine ⟨15041375372908905167881691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027583581939270111921127 15041375372908905167881691)
            ·
              refine ⟨22562063059363357751822537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15041375372908905167881691 22562063059363357751822537)
              ·
                refine ⟨16921547294522518313866903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22562063059363357751822537 16921547294522518313866903)
                ·
                  refine ⟨25382320941783777470800355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16921547294522518313866903 25382320941783777470800355)
                  ·
                    refine ⟨38073481412675666206200533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25382320941783777470800355 38073481412675666206200533)
                    ·
                      refine ⟨892347220609585926707825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38073481412675666206200533 892347220609585926707825)
                      ·
                        rfl

theorem cell23_1737840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1737840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737840 prefixEnd_1737840 := by exact prefixLift 1737840
  have htrace : WordTrace (prefixWord ++ tailWord_1737840) baseStart_1737840 baseEnd_1737840 := by
    simpa [prefixWord, tailWord_1737840, baseEnd_1737840] using wordTrace_append hprefix tailTrace_1737840
  have hstable : (prefixWord ++ tailWord_1737840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737840).length < 2 ^ (prefixWord ++ tailWord_1737840).sum := by decide
  have hdescent : baseEnd_1737840 < baseStart_1737840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737847 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 2, 5]
def baseStart_1737847 : Nat := 118140960795 + 1737847 * 2 ^ 59
def prefixEnd_1737847 : Nat := 4983230072969 + 3 ^ 40 * 1737847 * 2
def baseEnd_1737847 : Nat := 297450271658055799773431

theorem tailTrace_1737847 : CollatzResearch.WordTrace tailWord_1737847 prefixEnd_1737847 297450271658055799773431 := by
  unfold tailWord_1737847
  simp only [CollatzResearch.WordTrace]
  refine ⟨63384487335084594483203795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42256324890056396322135863 63384487335084594483203795)
  ·
    refine ⟨95076731002626891724805693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63384487335084594483203795 95076731002626891724805693)
    ·
      refine ⟨35653774125985084396802135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95076731002626891724805693 35653774125985084396802135)
      ·
        refine ⟨53480661188977626595203203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35653774125985084396802135 53480661188977626595203203)
        ·
          refine ⟨80220991783466439892804805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53480661188977626595203203 80220991783466439892804805)
          ·
            refine ⟨15041435959399957479900901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80220991783466439892804805 15041435959399957479900901)
            ·
              refine ⟨2820269242387492027481419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15041435959399957479900901 2820269242387492027481419)
              ·
                refine ⟨4230403863581238041222129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820269242387492027481419 4230403863581238041222129)
                ·
                  refine ⟨3172802897685928530916597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230403863581238041222129 3172802897685928530916597)
                  ·
                    refine ⟨297450271658055799773431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3172802897685928530916597 297450271658055799773431)
                    ·
                      rfl

theorem cell23_1737847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_1737847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737847 prefixEnd_1737847 := by exact prefixLift 1737847
  have htrace : WordTrace (prefixWord ++ tailWord_1737847) baseStart_1737847 baseEnd_1737847 := by
    simpa [prefixWord, tailWord_1737847, baseEnd_1737847] using wordTrace_append hprefix tailTrace_1737847
  have hstable : (prefixWord ++ tailWord_1737847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737847).length < 2 ^ (prefixWord ++ tailWord_1737847).sum := by decide
  have hdescent : baseEnd_1737847 < baseStart_1737847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737857 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1737857 : Nat := 118140960795 + 1737857 * 2 ^ 59
def prefixEnd_1737857 : Nat := 4983230072969 + 3 ^ 40 * 1737857 * 2
def baseEnd_1737857 : Nat := 892355949780712360195247

theorem tailTrace_1737857 : CollatzResearch.WordTrace tailWord_1737857 prefixEnd_1737857 892355949780712360195247 := by
  unfold tailWord_1737857
  simp only [CollatzResearch.WordTrace]
  refine ⟨63384852065048366191067825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42256568043365577460711883 63384852065048366191067825)
  ·
    refine ⟨47538639048786274643300869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63384852065048366191067825 47538639048786274643300869)
    ·
      refine ⟨8913494821647426495618913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47538639048786274643300869 8913494821647426495618913)
      ·
        refine ⟨6685121116235569871714185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8913494821647426495618913 6685121116235569871714185)
        ·
          refine ⟨5013840837176677403785639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685121116235569871714185 5013840837176677403785639)
          ·
            refine ⟨7520761255765016105678459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013840837176677403785639 7520761255765016105678459)
            ·
              refine ⟨11281141883647524158517689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520761255765016105678459 11281141883647524158517689)
              ·
                refine ⟨8460856412735643118888267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11281141883647524158517689 8460856412735643118888267)
                ·
                  refine ⟨12691284619103464678332401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8460856412735643118888267 12691284619103464678332401)
                  ·
                    refine ⟨9518463464327598508749301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12691284619103464678332401 9518463464327598508749301)
                    ·
                      refine ⟨892355949780712360195247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9518463464327598508749301 892355949780712360195247)
                      ·
                        rfl

theorem cell23_1737857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1737857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737857 prefixEnd_1737857 := by exact prefixLift 1737857
  have htrace : WordTrace (prefixWord ++ tailWord_1737857) baseStart_1737857 baseEnd_1737857 := by
    simpa [prefixWord, tailWord_1737857, baseEnd_1737857] using wordTrace_append hprefix tailTrace_1737857
  have hstable : (prefixWord ++ tailWord_1737857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737857).length < 2 ^ (prefixWord ++ tailWord_1737857).sum := by decide
  have hdescent : baseEnd_1737857 < baseStart_1737857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737867 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 6, 2]
def baseStart_1737867 : Nat := 118140960795 + 1737867 * 2 ^ 59
def prefixEnd_1737867 : Nat := 4983230072969 + 3 ^ 40 * 1737867 * 2
def baseEnd_1737867 : Nat := 892361084587257321070201

theorem tailTrace_1737867 : CollatzResearch.WordTrace tailWord_1737867 prefixEnd_1737867 892361084587257321070201 := by
  unfold tailWord_1737867
  simp only [CollatzResearch.WordTrace]
  refine ⟨63385216795012137898931855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42256811196674758599287903 63385216795012137898931855)
  ·
    refine ⟨95077825192518206848397783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63385216795012137898931855 95077825192518206848397783)
    ·
      refine ⟨142616737788777310272596675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95077825192518206848397783 142616737788777310272596675)
      ·
        refine ⟨213925106683165965408895013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142616737788777310272596675 213925106683165965408895013)
        ·
          refine ⟨40110957503093618514167815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213925106683165965408895013 40110957503093618514167815)
          ·
            refine ⟨60166436254640427771251723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40110957503093618514167815 60166436254640427771251723)
            ·
              refine ⟨90249654381960641656877585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60166436254640427771251723 90249654381960641656877585)
              ·
                refine ⟨67687240786470481242658189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90249654381960641656877585 67687240786470481242658189)
                ·
                  refine ⟨25382715294926430465996821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67687240786470481242658189 25382715294926430465996821)
                  ·
                    refine ⟨1189814779449676428093601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25382715294926430465996821 1189814779449676428093601)
                    ·
                      refine ⟨892361084587257321070201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189814779449676428093601 892361084587257321070201)
                      ·
                        rfl

theorem cell23_1737867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6, 2].length) (baseStart_1737867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737867 prefixEnd_1737867 := by exact prefixLift 1737867
  have htrace : WordTrace (prefixWord ++ tailWord_1737867) baseStart_1737867 baseEnd_1737867 := by
    simpa [prefixWord, tailWord_1737867, baseEnd_1737867] using wordTrace_append hprefix tailTrace_1737867
  have hstable : (prefixWord ++ tailWord_1737867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737867).length < 2 ^ (prefixWord ++ tailWord_1737867).sum := by decide
  have hdescent : baseEnd_1737867 < baseStart_1737867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737884 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1737884 : Nat := 118140960795 + 1737884 * 2 ^ 59
def prefixEnd_1737884 : Nat := 4983230072969 + 3 ^ 40 * 1737884 * 2
def baseEnd_1737884 : Nat := 892369813758383754557623

theorem tailTrace_1737884 : CollatzResearch.WordTrace tailWord_1737884 prefixEnd_1737884 892369813758383754557623 := by
  unfold tailWord_1737884
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692918417975274901150353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42257224557300366534867137 31692918417975274901150353)
  ·
    refine ⟨23769688813481456175862765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31692918417975274901150353 23769688813481456175862765)
    ·
      refine ⟨8913633305055546065948537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23769688813481456175862765 8913633305055546065948537)
      ·
        refine ⟨6685224978791659549461403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8913633305055546065948537 6685224978791659549461403)
        ·
          refine ⟨10027837468187489324192105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685224978791659549461403 10027837468187489324192105)
          ·
            refine ⟨7520878101140616993144079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10027837468187489324192105 7520878101140616993144079)
            ·
              refine ⟨11281317151710925489716119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520878101140616993144079 11281317151710925489716119)
              ·
                refine ⟨16921975727566388234574179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281317151710925489716119 16921975727566388234574179)
                ·
                  refine ⟨25382963591349582351861269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16921975727566388234574179 25382963591349582351861269)
                  ·
                    refine ⟨1189826418344511672743497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25382963591349582351861269 1189826418344511672743497)
                    ·
                      refine ⟨892369813758383754557623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189826418344511672743497 892369813758383754557623)
                      ·
                        rfl

theorem cell23_1737884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1737884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737884 prefixEnd_1737884 := by exact prefixLift 1737884
  have htrace : WordTrace (prefixWord ++ tailWord_1737884) baseStart_1737884 baseEnd_1737884 := by
    simpa [prefixWord, tailWord_1737884, baseEnd_1737884] using wordTrace_append hprefix tailTrace_1737884
  have hstable : (prefixWord ++ tailWord_1737884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737884).length < 2 ^ (prefixWord ++ tailWord_1737884).sum := by decide
  have hdescent : baseEnd_1737884 < baseStart_1737884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737911 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 1, 4]
def baseStart_1737911 : Nat := 118140960795 + 1737911 * 2 ^ 59
def prefixEnd_1737911 : Nat := 4983230072969 + 3 ^ 40 * 1737911 * 2
def baseEnd_1737911 : Nat := 297461225912018382973333

theorem tailTrace_1737911 : CollatzResearch.WordTrace tailWord_1737911 prefixEnd_1737911 297461225912018382973333 := by
  unfold tailWord_1737911
  simp only [CollatzResearch.WordTrace]
  refine ⟨63386821606852733413533587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42257881071235155609022391 63386821606852733413533587)
  ·
    refine ⟨95080232410279100120300381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63386821606852733413533587 95080232410279100120300381)
    ·
      refine ⟨35655087153854662545112643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95080232410279100120300381 35655087153854662545112643)
      ·
        refine ⟨53482630730781993817668965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35655087153854662545112643 53482630730781993817668965)
        ·
          refine ⟨10027993262021623840812931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53482630730781993817668965 10027993262021623840812931)
          ·
            refine ⟨15041989893032435761219397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027993262021623840812931 15041989893032435761219397)
            ·
              refine ⟨2820373104943581705228637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15041989893032435761219397 2820373104943581705228637)
              ·
                refine ⟨1057639914353843139460739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820373104943581705228637 1057639914353843139460739)
                ·
                  refine ⟨1586459871530764709191109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057639914353843139460739 1586459871530764709191109)
                  ·
                    refine ⟨297461225912018382973333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586459871530764709191109 297461225912018382973333)
                    ·
                      rfl

theorem cell23_1737911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_1737911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737911 prefixEnd_1737911 := by exact prefixLift 1737911
  have htrace : WordTrace (prefixWord ++ tailWord_1737911) baseStart_1737911 baseEnd_1737911 := by
    simpa [prefixWord, tailWord_1737911, baseEnd_1737911] using wordTrace_append hprefix tailTrace_1737911
  have hstable : (prefixWord ++ tailWord_1737911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737911).length < 2 ^ (prefixWord ++ tailWord_1737911).sum := by decide
  have hdescent : baseEnd_1737911 < baseStart_1737911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737924 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 8]
def baseStart_1737924 : Nat := 118140960795 + 1737924 * 2 ^ 59
def prefixEnd_1737924 : Nat := 4983230072969 + 3 ^ 40 * 1737924 * 2
def baseEnd_1737924 : Nat := 99154483664951510895271

theorem tailTrace_1737924 : CollatzResearch.WordTrace tailWord_1737924 prefixEnd_1737924 99154483664951510895271 := by
  unfold tailWord_1737924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31693647877902818316878413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42258197170537091089171217 31693647877902818316878413)
  ·
    refine ⟨11885117954213556868829405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31693647877902818316878413 11885117954213556868829405)
    ·
      refine ⟨4456919232830083825811027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11885117954213556868829405 4456919232830083825811027)
      ·
        refine ⟨6685378849245125738716541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456919232830083825811027 6685378849245125738716541)
        ·
          refine ⟨2507017068466922152018703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6685378849245125738716541 2507017068466922152018703)
          ·
            refine ⟨3760525602700383228028055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507017068466922152018703 3760525602700383228028055)
            ·
              refine ⟨5640788404050574842042083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760525602700383228028055 5640788404050574842042083)
              ·
                refine ⟨8461182606075862263063125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640788404050574842042083 8461182606075862263063125)
                ·
                  refine ⟨99154483664951510895271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8461182606075862263063125 99154483664951510895271)
                  ·
                    rfl

theorem cell23_1737924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_1737924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737924 prefixEnd_1737924 := by exact prefixLift 1737924
  have htrace : WordTrace (prefixWord ++ tailWord_1737924) baseStart_1737924 baseEnd_1737924 := by
    simpa [prefixWord, tailWord_1737924, baseEnd_1737924] using wordTrace_append hprefix tailTrace_1737924
  have hstable : (prefixWord ++ tailWord_1737924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737924).length < 2 ^ (prefixWord ++ tailWord_1737924).sum := by decide
  have hdescent : baseEnd_1737924 < baseStart_1737924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737941 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 6]
def baseStart_1737941 : Nat := 118140960795 + 1737941 * 2 ^ 59
def prefixEnd_1737941 : Nat := 4983230072969 + 3 ^ 40 * 1737941 * 2
def baseEnd_1737941 : Nat := 99155453572854447949429

theorem tailTrace_1737941 : CollatzResearch.WordTrace tailWord_1737941 prefixEnd_1737941 99155453572854447949429 := by
  unfold tailWord_1737941
  simp only [CollatzResearch.WordTrace]
  refine ⟨63387915796744048537125677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42258610531162699024750451 63387915796744048537125677)
  ·
    refine ⟨23770468423779018201422129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63387915796744048537125677 23770468423779018201422129)
    ·
      refine ⟨17827851317834263651066597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23770468423779018201422129 17827851317834263651066597)
      ·
        refine ⟨3342722122093924434574987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17827851317834263651066597 3342722122093924434574987)
        ·
          refine ⟨5014083183140886651862481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342722122093924434574987 5014083183140886651862481)
          ·
            refine ⟨3760562387355664988896861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014083183140886651862481 3760562387355664988896861)
            ·
              refine ⟨1410210895258374370836323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3760562387355664988896861 1410210895258374370836323)
              ·
                refine ⟨2115316342887561556254485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410210895258374370836323 2115316342887561556254485)
                ·
                  refine ⟨99155453572854447949429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2115316342887561556254485 99155453572854447949429)
                  ·
                    rfl

theorem cell23_1737941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_1737941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737941 prefixEnd_1737941 := by exact prefixLift 1737941
  have htrace : WordTrace (prefixWord ++ tailWord_1737941) baseStart_1737941 baseEnd_1737941 := by
    simpa [prefixWord, tailWord_1737941, baseEnd_1737941] using wordTrace_append hprefix tailTrace_1737941
  have hstable : (prefixWord ++ tailWord_1737941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737941).length < 2 ^ (prefixWord ++ tailWord_1737941).sum := by decide
  have hdescent : baseEnd_1737941 < baseStart_1737941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737974 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1737974 : Nat := 118140960795 + 1737974 * 2 ^ 59
def prefixEnd_1737974 : Nat := 4983230072969 + 3 ^ 40 * 1737974 * 2
def baseEnd_1737974 : Nat := 892416027017288402432209

theorem tailTrace_1737974 : CollatzResearch.WordTrace tailWord_1737974 prefixEnd_1737974 892416027017288402432209 := by
  unfold tailWord_1737974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961819962851530948317311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42259412937082996782051317 3961819962851530948317311)
  ·
    refine ⟨5942729944277296422475967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961819962851530948317311 5942729944277296422475967)
    ·
      refine ⟨8914094916415944633713951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942729944277296422475967 8914094916415944633713951)
      ·
        refine ⟨13371142374623916950570927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914094916415944633713951 13371142374623916950570927)
        ·
          refine ⟨20056713561935875425856391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371142374623916950570927 20056713561935875425856391)
          ·
            refine ⟨30085070342903813138784587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056713561935875425856391 30085070342903813138784587)
            ·
              refine ⟨45127605514355719708176881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30085070342903813138784587 45127605514355719708176881)
              ·
                refine ⟨33845704135766789781132661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45127605514355719708176881 33845704135766789781132661)
                ·
                  refine ⟨3173034762728136541981187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33845704135766789781132661 3173034762728136541981187)
                  ·
                    refine ⟨4759552144092204812971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173034762728136541981187 4759552144092204812971781)
                    ·
                      refine ⟨892416027017288402432209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4759552144092204812971781 892416027017288402432209)
                      ·
                        rfl

theorem cell23_1737974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1737974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737974 prefixEnd_1737974 := by exact prefixLift 1737974
  have htrace : WordTrace (prefixWord ++ tailWord_1737974) baseStart_1737974 baseEnd_1737974 := by
    simpa [prefixWord, tailWord_1737974, baseEnd_1737974] using wordTrace_append hprefix tailTrace_1737974
  have hstable : (prefixWord ++ tailWord_1737974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737974).length < 2 ^ (prefixWord ++ tailWord_1737974).sum := by decide
  have hdescent : baseEnd_1737974 < baseStart_1737974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737984 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_1737984 : Nat := 118140960795 + 1737984 * 2 ^ 59
def prefixEnd_1737984 : Nat := 4983230072969 + 3 ^ 40 * 1737984 * 2
def baseEnd_1737984 : Nat := 297473720607944454435721

theorem tailTrace_1737984 : CollatzResearch.WordTrace tailWord_1737984 prefixEnd_1737984 297473720607944454435721 := by
  unfold tailWord_1737984
  simp only [CollatzResearch.WordTrace]
  refine ⟨31694742067794133440470503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42259656090392177920627337 31694742067794133440470503)
  ·
    refine ⟨47542113101691200160705755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31694742067794133440470503 47542113101691200160705755)
    ·
      refine ⟨71313169652536800241058633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47542113101691200160705755 71313169652536800241058633)
      ·
        refine ⟨53484877239402600180793975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71313169652536800241058633 53484877239402600180793975)
        ·
          refine ⟨80227315859103900271190963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53484877239402600180793975 80227315859103900271190963)
          ·
            refine ⟨120340973788655850406786445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80227315859103900271190963 120340973788655850406786445)
            ·
              refine ⟨45127865170745943902544917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120340973788655850406786445 45127865170745943902544917)
              ·
                refine ⟨2115368679878716120431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45127865170745943902544917 2115368679878716120431793)
                ·
                  refine ⟨1586526509909037090323845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2115368679878716120431793 1586526509909037090323845)
                  ·
                    refine ⟨297473720607944454435721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586526509909037090323845 297473720607944454435721)
                    ·
                      rfl

theorem cell23_1737984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_1737984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737984 prefixEnd_1737984 := by exact prefixLift 1737984
  have htrace : WordTrace (prefixWord ++ tailWord_1737984) baseStart_1737984 baseEnd_1737984 := by
    simpa [prefixWord, tailWord_1737984, baseEnd_1737984] using wordTrace_append hprefix tailTrace_1737984
  have hstable : (prefixWord ++ tailWord_1737984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737984).length < 2 ^ (prefixWord ++ tailWord_1737984).sum := by decide
  have hdescent : baseEnd_1737984 < baseStart_1737984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737985 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_1737985 : Nat := 118140960795 + 1737985 * 2 ^ 59
def prefixEnd_1737985 : Nat := 4983230072969 + 3 ^ 40 * 1737985 * 2
def baseEnd_1737985 : Nat := 892421675304487859394659

theorem tailTrace_1737985 : CollatzResearch.WordTrace tailWord_1737985 prefixEnd_1737985 892421675304487859394659 := by
  unfold tailWord_1737985
  simp only [CollatzResearch.WordTrace]
  refine ⟨63389520608584644051727409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42259680405723096034484939 63389520608584644051727409)
  ·
    refine ⟨47542140456438483038795557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63389520608584644051727409 47542140456438483038795557)
    ·
      refine ⟨8914151335582215569774167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47542140456438483038795557 8914151335582215569774167)
      ·
        refine ⟨13371227003373323354661251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914151335582215569774167 13371227003373323354661251)
        ·
          refine ⟨20056840505059985031991877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371227003373323354661251 20056840505059985031991877)
          ·
            refine ⟨3760657594698747193498477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20056840505059985031991877 3760657594698747193498477)
            ·
              refine ⟨1410246598012030197561929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3760657594698747193498477 1410246598012030197561929)
              ·
                refine ⟨1057684948509022648171447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410246598012030197561929 1057684948509022648171447)
                ·
                  refine ⟨1586527422763533972257171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057684948509022648171447 1586527422763533972257171)
                  ·
                    refine ⟨2379791134145300958385757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586527422763533972257171 2379791134145300958385757)
                    ·
                      refine ⟨892421675304487859394659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2379791134145300958385757 892421675304487859394659)
                      ·
                        rfl

theorem cell23_1737985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_1737985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737985 prefixEnd_1737985 := by exact prefixLift 1737985
  have htrace : WordTrace (prefixWord ++ tailWord_1737985) baseStart_1737985 baseEnd_1737985 := by
    simpa [prefixWord, tailWord_1737985, baseEnd_1737985] using wordTrace_append hprefix tailTrace_1737985
  have hstable : (prefixWord ++ tailWord_1737985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737985).length < 2 ^ (prefixWord ++ tailWord_1737985).sum := by decide
  have hdescent : baseEnd_1737985 < baseStart_1737985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737987 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1737987 : Nat := 118140960795 + 1737987 * 2 ^ 59
def prefixEnd_1737987 : Nat := 4983230072969 + 3 ^ 40 * 1737987 * 2
def baseEnd_1737987 : Nat := 892422702265796851569649

theorem tailTrace_1737987 : CollatzResearch.WordTrace tailWord_1737987 prefixEnd_1737987 892422702265796851569649 := by
  unfold tailWord_1737987
  simp only [CollatzResearch.WordTrace]
  refine ⟨63389593554577398393300215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42259729036384932262200143 63389593554577398393300215)
  ·
    refine ⟨95084390331866097589950323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63389593554577398393300215 95084390331866097589950323)
    ·
      refine ⟨142626585497799146384925485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95084390331866097589950323 142626585497799146384925485)
      ·
        refine ⟨53484969561674679894347057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142626585497799146384925485 53484969561674679894347057)
        ·
          refine ⟨40113727171256009920760293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53484969561674679894347057 40113727171256009920760293)
          ·
            refine ⟨7521323844610501860142555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40113727171256009920760293 7521323844610501860142555)
            ·
              refine ⟨11281985766915752790213833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521323844610501860142555 11281985766915752790213833)
              ·
                refine ⟨8461489325186814592660375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11281985766915752790213833 8461489325186814592660375)
                ·
                  refine ⟨12692233987780221888990563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461489325186814592660375 12692233987780221888990563)
                  ·
                    refine ⟨19038350981670332833485845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12692233987780221888990563 19038350981670332833485845)
                    ·
                      refine ⟨892422702265796851569649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19038350981670332833485845 892422702265796851569649)
                      ·
                        rfl

theorem cell23_1737987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1737987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737987 prefixEnd_1737987 := by exact prefixLift 1737987
  have htrace : WordTrace (prefixWord ++ tailWord_1737987) baseStart_1737987 baseEnd_1737987 := by
    simpa [prefixWord, tailWord_1737987, baseEnd_1737987] using wordTrace_append hprefix tailTrace_1737987
  have hstable : (prefixWord ++ tailWord_1737987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737987).length < 2 ^ (prefixWord ++ tailWord_1737987).sum := by decide
  have hdescent : baseEnd_1737987 < baseStart_1737987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737994 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1737994 : Nat := 118140960795 + 1737994 * 2 ^ 59
def prefixEnd_1737994 : Nat := 4983230072969 + 3 ^ 40 * 1737994 * 2
def baseEnd_1737994 : Nat := 892426296630378324182117

theorem tailTrace_1737994 : CollatzResearch.WordTrace tailWord_1737994 prefixEnd_1737994 892426296630378324182117 := by
  unfold tailWord_1737994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847462216388009647201259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42259899243701359059203357 15847462216388009647201259)
  ·
    refine ⟨23771193324582014470801889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15847462216388009647201259 23771193324582014470801889)
    ·
      refine ⟨17828394993436510853101417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23771193324582014470801889 17828394993436510853101417)
      ·
        refine ⟨13371296245077383139826063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17828394993436510853101417 13371296245077383139826063)
        ·
          refine ⟨20056944367616074709739095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371296245077383139826063 20056944367616074709739095)
          ·
            refine ⟨30085416551424112064608643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056944367616074709739095 30085416551424112064608643)
            ·
              refine ⟨45128124827136168096912965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30085416551424112064608643 45128124827136168096912965)
              ·
                refine ⟨8461523405088031518171181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45128124827136168096912965 8461523405088031518171181)
                ·
                  refine ⟨3173071276908011819314193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8461523405088031518171181 3173071276908011819314193)
                  ·
                    refine ⟨2379803457681008864485645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173071276908011819314193 2379803457681008864485645)
                    ·
                      refine ⟨892426296630378324182117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2379803457681008864485645 892426296630378324182117)
                      ·
                        rfl

theorem cell23_1737994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1737994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1737994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1737994 prefixEnd_1737994 := by exact prefixLift 1737994
  have htrace : WordTrace (prefixWord ++ tailWord_1737994) baseStart_1737994 baseEnd_1737994 := by
    simpa [prefixWord, tailWord_1737994, baseEnd_1737994] using wordTrace_append hprefix tailTrace_1737994
  have hstable : (prefixWord ++ tailWord_1737994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737994).length < 2 ^ (prefixWord ++ tailWord_1737994).sum := by decide
  have hdescent : baseEnd_1737994 < baseStart_1737994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738057 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_1738057 : Nat := 118140960795 + 1738057 * 2 ^ 59
def prefixEnd_1738057 : Nat := 4983230072969 + 3 ^ 40 * 1738057 * 2
def baseEnd_1738057 : Nat := 297486215303870525898109

theorem tailTrace_1738057 : CollatzResearch.WordTrace tailWord_1738057 prefixEnd_1738057 297486215303870525898109 := by
  unfold tailWord_1738057
  simp only [CollatzResearch.WordTrace]
  refine ⟨63392146664323800348348425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42261431109549200232232283 63392146664323800348348425)
  ·
    refine ⟨47544109998242850261261319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63392146664323800348348425 47544109998242850261261319)
    ·
      refine ⟨71316164997364275391891979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47544109998242850261261319 71316164997364275391891979)
      ·
        refine ⟨106974247496046413087837969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71316164997364275391891979 106974247496046413087837969)
        ·
          refine ⟨80230685622034809815878477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106974247496046413087837969 80230685622034809815878477)
          ·
            refine ⟨30086507108263053680954429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80230685622034809815878477 30086507108263053680954429)
            ·
              refine ⟨11282440165598645130357911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30086507108263053680954429 11282440165598645130357911)
              ·
                refine ⟨16923660248397967695536867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282440165598645130357911 16923660248397967695536867)
                ·
                  refine ⟨25385490372596951543305301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16923660248397967695536867 25385490372596951543305301)
                  ·
                    refine ⟨297486215303870525898109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25385490372596951543305301 297486215303870525898109)
                    ·
                      rfl

theorem cell23_1738057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_1738057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738057 prefixEnd_1738057 := by exact prefixLift 1738057
  have htrace : WordTrace (prefixWord ++ tailWord_1738057) baseStart_1738057 baseEnd_1738057 := by
    simpa [prefixWord, tailWord_1738057, baseEnd_1738057] using wordTrace_append hprefix tailTrace_1738057
  have hstable : (prefixWord ++ tailWord_1738057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738057).length < 2 ^ (prefixWord ++ tailWord_1738057).sum := by decide
  have hdescent : baseEnd_1738057 < baseStart_1738057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738068 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_1738068 : Nat := 118140960795 + 1738068 * 2 ^ 59
def prefixEnd_1738068 : Nat := 4983230072969 + 3 ^ 40 * 1738068 * 2
def baseEnd_1738068 : Nat := 892464294198811034656777

theorem tailTrace_1738068 : CollatzResearch.WordTrace tailWord_1738068 prefixEnd_1738068 892464294198811034656777 := by
  unfold tailWord_1738068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31696273933641974613499429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42261698578189299484665905 31696273933641974613499429)
  ·
    refine ⟨5943051362557870240031143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31696273933641974613499429 5943051362557870240031143)
    ·
      refine ⟨8914577043836805360046715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943051362557870240031143 8914577043836805360046715)
      ·
        refine ⟨13371865565755208040070073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914577043836805360046715 13371865565755208040070073)
        ·
          refine ⟨10028899174316406030052555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371865565755208040070073 10028899174316406030052555)
          ·
            refine ⟨15043348761474609045078833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10028899174316406030052555 15043348761474609045078833)
            ·
              refine ⟨11282511571105956783809125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15043348761474609045078833 11282511571105956783809125)
              ·
                refine ⟨2115470919582366896964211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11282511571105956783809125 2115470919582366896964211)
                ·
                  refine ⟨3173206379373550345446317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115470919582366896964211 3173206379373550345446317)
                  ·
                    refine ⟨1189952392265081379542369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173206379373550345446317 1189952392265081379542369)
                    ·
                      refine ⟨892464294198811034656777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189952392265081379542369 892464294198811034656777)
                      ·
                        rfl

theorem cell23_1738068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_1738068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738068 prefixEnd_1738068 := by exact prefixLift 1738068
  have htrace : WordTrace (prefixWord ++ tailWord_1738068) baseStart_1738068 baseEnd_1738068 := by
    simpa [prefixWord, tailWord_1738068, baseEnd_1738068] using wordTrace_append hprefix tailTrace_1738068
  have hstable : (prefixWord ++ tailWord_1738068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738068).length < 2 ^ (prefixWord ++ tailWord_1738068).sum := by decide
  have hdescent : baseEnd_1738068 < baseStart_1738068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738098 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1738098 : Nat := 118140960795 + 1738098 * 2 ^ 59
def prefixEnd_1738098 : Nat := 4983230072969 + 3 ^ 40 * 1738098 * 2
def baseEnd_1738098 : Nat := 892479698618445917281639

theorem tailTrace_1738098 : CollatzResearch.WordTrace tailWord_1738098 prefixEnd_1738098 892479698618445917281639 := by
  unfold tailWord_1738098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848410514293816087647737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42262428038116842900393965 15848410514293816087647737)
  ·
    refine ⟨11886307885720362065735803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15848410514293816087647737 11886307885720362065735803)
    ·
      refine ⟨17829461828580543098603705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11886307885720362065735803 17829461828580543098603705)
      ·
        refine ⟨13372096371435407323952779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17829461828580543098603705 13372096371435407323952779)
        ·
          refine ⟨20058144557153110985929169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13372096371435407323952779 20058144557153110985929169)
          ·
            refine ⟨15043608417864833239446877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20058144557153110985929169 15043608417864833239446877)
            ·
              refine ⟨5641353156699312464792579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15043608417864833239446877 5641353156699312464792579)
              ·
                refine ⟨8462029735048968697188869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641353156699312464792579 8462029735048968697188869)
                ·
                  refine ⟨1586630575321681630722913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8462029735048968697188869 1586630575321681630722913)
                  ·
                    refine ⟨1189972931491261223042185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586630575321681630722913 1189972931491261223042185)
                    ·
                      refine ⟨892479698618445917281639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1189972931491261223042185 892479698618445917281639)
                      ·
                        rfl

theorem cell23_1738098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1738098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738098 prefixEnd_1738098 := by exact prefixLift 1738098
  have htrace : WordTrace (prefixWord ++ tailWord_1738098) baseStart_1738098 baseEnd_1738098 := by
    simpa [prefixWord, tailWord_1738098, baseEnd_1738098] using wordTrace_append hprefix tailTrace_1738098
  have hstable : (prefixWord ++ tailWord_1738098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738098).length < 2 ^ (prefixWord ++ tailWord_1738098).sum := by decide
  have hdescent : baseEnd_1738098 < baseStart_1738098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738144 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1738144 : Nat := 118140960795 + 1738144 * 2 ^ 59
def prefixEnd_1738144 : Nat := 4983230072969 + 3 ^ 40 * 1738144 * 2
def baseEnd_1738144 : Nat := 892503318728552737306427

theorem tailTrace_1738144 : CollatzResearch.WordTrace tailWord_1738144 prefixEnd_1738144 892503318728552737306427 := by
  unfold tailWord_1738144
  simp only [CollatzResearch.WordTrace]
  refine ⟨31697659907504307103382743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42263546543339076137843657 31697659907504307103382743)
  ·
    refine ⟨47546489861256460655074115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31697659907504307103382743 47546489861256460655074115)
    ·
      refine ⟨71319734791884690982611173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47546489861256460655074115 71319734791884690982611173)
      ·
        refine ⟨13372450273478379559239595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71319734791884690982611173 13372450273478379559239595)
        ·
          refine ⟨20058675410217569338859393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13372450273478379559239595 20058675410217569338859393)
          ·
            refine ⟨15044006557663177004144545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20058675410217569338859393 15044006557663177004144545)
            ·
              refine ⟨11283004918247382753108409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15044006557663177004144545 11283004918247382753108409)
              ·
                refine ⟨8462253688685537064831307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11283004918247382753108409 8462253688685537064831307)
                ·
                  refine ⟨12693380533028305597246961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8462253688685537064831307 12693380533028305597246961)
                  ·
                    refine ⟨9520035399771229197935221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12693380533028305597246961 9520035399771229197935221)
                    ·
                      refine ⟨892503318728552737306427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9520035399771229197935221 892503318728552737306427)
                      ·
                        rfl

theorem cell23_1738144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1738144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738144 prefixEnd_1738144 := by exact prefixLift 1738144
  have htrace : WordTrace (prefixWord ++ tailWord_1738144) baseStart_1738144 baseEnd_1738144 := by
    simpa [prefixWord, tailWord_1738144, baseEnd_1738144] using wordTrace_append hprefix tailTrace_1738144
  have hstable : (prefixWord ++ tailWord_1738144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738144).length < 2 ^ (prefixWord ++ tailWord_1738144).sum := by decide
  have hdescent : baseEnd_1738144 < baseStart_1738144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738151 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1738151 : Nat := 118140960795 + 1738151 * 2 ^ 59
def prefixEnd_1738151 : Nat := 4983230072969 + 3 ^ 40 * 1738151 * 2
def baseEnd_1738151 : Nat := 297502304364378069972965

theorem tailTrace_1738151 : CollatzResearch.WordTrace tailWord_1738151 prefixEnd_1738151 297502304364378069972965 := by
  unfold tailWord_1738151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63395575125983254402270307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42263716750655502934846871 63395575125983254402270307)
  ·
    refine ⟨95093362688974881603405461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63395575125983254402270307 95093362688974881603405461)
    ·
      refine ⟨4457501376045697575159631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95093362688974881603405461 4457501376045697575159631)
      ·
        refine ⟨6686252064068546362739447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457501376045697575159631 6686252064068546362739447)
        ·
          refine ⟨10029378096102819544109171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686252064068546362739447 10029378096102819544109171)
          ·
            refine ⟨15044067144154229316163757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029378096102819544109171 15044067144154229316163757)
            ·
              refine ⟨5641525179057835993561409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15044067144154229316163757 5641525179057835993561409)
              ·
                refine ⟨4231143884293376995171057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641525179057835993561409 4231143884293376995171057)
                ·
                  refine ⟨3173357913220032746378293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231143884293376995171057 3173357913220032746378293)
                  ·
                    refine ⟨297502304364378069972965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3173357913220032746378293 297502304364378069972965)
                    ·
                      rfl

theorem cell23_1738151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1738151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738151 prefixEnd_1738151 := by exact prefixLift 1738151
  have htrace : WordTrace (prefixWord ++ tailWord_1738151) baseStart_1738151 baseEnd_1738151 := by
    simpa [prefixWord, tailWord_1738151, baseEnd_1738151] using wordTrace_append hprefix tailTrace_1738151
  have hstable : (prefixWord ++ tailWord_1738151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738151).length < 2 ^ (prefixWord ++ tailWord_1738151).sum := by decide
  have hdescent : baseEnd_1738151 < baseStart_1738151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738188 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1738188 : Nat := 118140960795 + 1738188 * 2 ^ 59
def prefixEnd_1738188 : Nat := 4983230072969 + 3 ^ 40 * 1738188 * 2
def baseEnd_1738188 : Nat := 892525911877350565156225

theorem tailTrace_1738188 : CollatzResearch.WordTrace tailWord_1738188 prefixEnd_1738188 892525911877350565156225 := by
  unfold tailWord_1738188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31698462313424604860683609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42264616417899473147578145 31698462313424604860683609)
  ·
    refine ⟨23773846735068453645512707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31698462313424604860683609 23773846735068453645512707)
    ·
      refine ⟨35660770102602680468269061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23773846735068453645512707 35660770102602680468269061)
      ·
        refine ⟨6686394394238002587800449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35660770102602680468269061 6686394394238002587800449)
        ·
          refine ⟨5014795795678501940850337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686394394238002587800449 5014795795678501940850337)
          ·
            refine ⟨3761096846758876455637753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014795795678501940850337 3761096846758876455637753)
            ·
              refine ⟨2820822635069157341728315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761096846758876455637753 2820822635069157341728315)
              ·
                refine ⟨4231233952603736012592473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820822635069157341728315 4231233952603736012592473)
                ·
                  refine ⟨3173425464452802009444355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231233952603736012592473 3173425464452802009444355)
                  ·
                    refine ⟨4760138196679203014166533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3173425464452802009444355 4760138196679203014166533)
                    ·
                      refine ⟨892525911877350565156225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4760138196679203014166533 892525911877350565156225)
                      ·
                        rfl

theorem cell23_1738188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1738188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738188 prefixEnd_1738188 := by exact prefixLift 1738188
  have htrace : WordTrace (prefixWord ++ tailWord_1738188) baseStart_1738188 baseEnd_1738188 := by
    simpa [prefixWord, tailWord_1738188, baseEnd_1738188] using wordTrace_append hprefix tailTrace_1738188
  have hstable : (prefixWord ++ tailWord_1738188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738188).length < 2 ^ (prefixWord ++ tailWord_1738188).sum := by decide
  have hdescent : baseEnd_1738188 < baseStart_1738188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738191 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_1738191 : Nat := 118140960795 + 1738191 * 2 ^ 59
def prefixEnd_1738191 : Nat := 4983230072969 + 3 ^ 40 * 1738191 * 2
def baseEnd_1738191 : Nat := 892527452319314053418711

theorem tailTrace_1738191 : CollatzResearch.WordTrace tailWord_1738191 prefixEnd_1738191 892527452319314053418711 := by
  unfold tailWord_1738191
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397034045838341233726427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42264689363892227489150951 63397034045838341233726427)
  ·
    refine ⟨95095551068757511850589641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63397034045838341233726427 95095551068757511850589641)
    ·
      refine ⟨71321663301568133887942231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95095551068757511850589641 71321663301568133887942231)
      ·
        refine ⟨106982494952352200831913347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71321663301568133887942231 106982494952352200831913347)
        ·
          refine ⟨160473742428528301247870021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106982494952352200831913347 160473742428528301247870021)
          ·
            refine ⟨30088826705349056483975629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160473742428528301247870021 30088826705349056483975629)
            ·
              refine ⟨11283310014505896181490861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30088826705349056483975629 11283310014505896181490861)
              ·
                refine ⟨4231241255439711068059073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11283310014505896181490861 4231241255439711068059073)
                ·
                  refine ⟨3173430941579783301044305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231241255439711068059073 3173430941579783301044305)
                  ·
                    refine ⟨2380073206184837475783229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173430941579783301044305 2380073206184837475783229)
                    ·
                      refine ⟨892527452319314053418711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380073206184837475783229 892527452319314053418711)
                      ·
                        rfl

theorem cell23_1738191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_1738191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738191 prefixEnd_1738191 := by exact prefixLift 1738191
  have htrace : WordTrace (prefixWord ++ tailWord_1738191) baseStart_1738191 baseEnd_1738191 := by
    simpa [prefixWord, tailWord_1738191, baseEnd_1738191] using wordTrace_append hprefix tailTrace_1738191
  have hstable : (prefixWord ++ tailWord_1738191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738191).length < 2 ^ (prefixWord ++ tailWord_1738191).sum := by decide
  have hdescent : baseEnd_1738191 < baseStart_1738191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738211 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 6]
def baseStart_1738211 : Nat := 118140960795 + 1738211 * 2 ^ 59
def prefixEnd_1738211 : Nat := 4983230072969 + 3 ^ 40 * 1738211 * 2
def baseEnd_1738211 : Nat := 99170857992489330574291

theorem tailTrace_1738211 : CollatzResearch.WordTrace tailWord_1738211 prefixEnd_1738211 99170857992489330574291 := by
  unfold tailWord_1738211
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397763505765884649454487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42265175670510589766302991 63397763505765884649454487)
  ·
    refine ⟨95096645258648826974181731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63397763505765884649454487 95096645258648826974181731)
    ·
      refine ⟨142644967887973240461272597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95096645258648826974181731 142644967887973240461272597)
      ·
        refine ⟨6686482869748745646622153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142644967887973240461272597 6686482869748745646622153)
        ·
          refine ⟨5014862152311559234966615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686482869748745646622153 5014862152311559234966615)
          ·
            refine ⟨7522293228467338852449923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014862152311559234966615 7522293228467338852449923)
            ·
              refine ⟨11283439842701008278674885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7522293228467338852449923 11283439842701008278674885)
              ·
                refine ⟨2115644970506439052251541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11283439842701008278674885 2115644970506439052251541)
                ·
                  refine ⟨99170857992489330574291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2115644970506439052251541 99170857992489330574291)
                  ·
                    rfl

theorem cell23_1738211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 6].length) (baseStart_1738211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738211 prefixEnd_1738211 := by exact prefixLift 1738211
  have htrace : WordTrace (prefixWord ++ tailWord_1738211) baseStart_1738211 baseEnd_1738211 := by
    simpa [prefixWord, tailWord_1738211, baseEnd_1738211] using wordTrace_append hprefix tailTrace_1738211
  have hstable : (prefixWord ++ tailWord_1738211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738211).length < 2 ^ (prefixWord ++ tailWord_1738211).sum := by decide
  have hdescent : baseEnd_1738211 < baseStart_1738211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738215 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1738215 : Nat := 118140960795 + 1738215 * 2 ^ 59
def prefixEnd_1738215 : Nat := 4983230072969 + 3 ^ 40 * 1738215 * 2
def baseEnd_1738215 : Nat := 297513258618340653172867

theorem tailTrace_1738215 : CollatzResearch.WordTrace tailWord_1738215 prefixEnd_1738215 297513258618340653172867 := by
  unfold tailWord_1738215
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397909397751393332600099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42265272931834262221733399 63397909397751393332600099)
  ·
    refine ⟨95096864096627089998900149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63397909397751393332600099 95096864096627089998900149)
    ·
      refine ⟨8915331009058789687396889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95096864096627089998900149 8915331009058789687396889)
      ·
        refine ⟨6686498256794092265547667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8915331009058789687396889 6686498256794092265547667)
        ·
          refine ⟨10029747385191138398321501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686498256794092265547667 10029747385191138398321501)
          ·
            refine ⟨3761155269446676899370563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10029747385191138398321501 3761155269446676899370563)
            ·
              refine ⟨5641732904170015349055845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761155269446676899370563 5641732904170015349055845)
              ·
                refine ⟨1057824919531877877947971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5641732904170015349055845 1057824919531877877947971)
                ·
                  refine ⟨1586737379297816816921957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057824919531877877947971 1586737379297816816921957)
                  ·
                    refine ⟨297513258618340653172867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586737379297816816921957 297513258618340653172867)
                    ·
                      rfl

theorem cell23_1738215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1738215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738215 prefixEnd_1738215 := by exact prefixLift 1738215
  have htrace : WordTrace (prefixWord ++ tailWord_1738215) baseStart_1738215 baseEnd_1738215 := by
    simpa [prefixWord, tailWord_1738215, baseEnd_1738215] using wordTrace_append hprefix tailTrace_1738215
  have hstable : (prefixWord ++ tailWord_1738215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738215).length < 2 ^ (prefixWord ++ tailWord_1738215).sum := by decide
  have hdescent : baseEnd_1738215 < baseStart_1738215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738234 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1738234 : Nat := 118140960795 + 1738234 * 2 ^ 59
def prefixEnd_1738234 : Nat := 4983230072969 + 3 ^ 40 * 1738234 * 2
def baseEnd_1738234 : Nat := 892549531987457385181013

theorem tailTrace_1738234 : CollatzResearch.WordTrace tailWord_1738234 prefixEnd_1738234 892549531987457385181013 := by
  unfold tailWord_1738234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849650596170639894385439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42265734923121706385027837 15849650596170639894385439)
  ·
    refine ⟨23774475894255959841578159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15849650596170639894385439 23774475894255959841578159)
    ·
      refine ⟨35661713841383939762367239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23774475894255959841578159 35661713841383939762367239)
      ·
        refine ⟨53492570762075909643550859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35661713841383939762367239 53492570762075909643550859)
        ·
          refine ⟨80238856143113864465326289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53492570762075909643550859 80238856143113864465326289)
          ·
            refine ⟨60179142107335398348994717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80238856143113864465326289 60179142107335398348994717)
            ·
              refine ⟨22567178290250774380873019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60179142107335398348994717 22567178290250774380873019)
              ·
                refine ⟨33850767435376161571309529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22567178290250774380873019 33850767435376161571309529)
                ·
                  refine ⟨25388075576532121178482147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33850767435376161571309529 25388075576532121178482147)
                  ·
                    refine ⟨38082113364798181767723221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25388075576532121178482147 38082113364798181767723221)
                    ·
                      refine ⟨892549531987457385181013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38082113364798181767723221 892549531987457385181013)
                      ·
                        rfl

theorem cell23_1738234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1738234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738234 prefixEnd_1738234 := by exact prefixLift 1738234
  have htrace : WordTrace (prefixWord ++ tailWord_1738234) baseStart_1738234 baseEnd_1738234 := by
    simpa [prefixWord, tailWord_1738234, baseEnd_1738234] using wordTrace_append hprefix tailTrace_1738234
  have hstable : (prefixWord ++ tailWord_1738234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738234).length < 2 ^ (prefixWord ++ tailWord_1738234).sum := by decide
  have hdescent : baseEnd_1738234 < baseStart_1738234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738242 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1738242 : Nat := 118140960795 + 1738242 * 2 ^ 59
def prefixEnd_1738242 : Nat := 4983230072969 + 3 ^ 40 * 1738242 * 2
def baseEnd_1738242 : Nat := 892553639832693353880977

theorem tailTrace_1738242 : CollatzResearch.WordTrace tailWord_1738242 prefixEnd_1738242 892553639832693353880977 := by
  unfold tailWord_1738242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849723542163394235958245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42265929445769051295888653 15849723542163394235958245)
  ·
    refine ⟨2971823164155636419242171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15849723542163394235958245 2971823164155636419242171)
    ·
      refine ⟨4457734746233454628863257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971823164155636419242171 4457734746233454628863257)
      ·
        refine ⟨3343301059675090971647443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4457734746233454628863257 3343301059675090971647443)
        ·
          refine ⟨5014951589512636457471165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343301059675090971647443 5014951589512636457471165)
          ·
            refine ⟨1880606846067238671551687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5014951589512636457471165 1880606846067238671551687)
            ·
              refine ⟨2820910269100858007327531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880606846067238671551687 2820910269100858007327531)
              ·
                refine ⟨4231365403651287010991297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820910269100858007327531 4231365403651287010991297)
                ·
                  refine ⟨3173524052738465258243473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231365403651287010991297 3173524052738465258243473)
                  ·
                    refine ⟨2380143039553848943682605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173524052738465258243473 2380143039553848943682605)
                    ·
                      refine ⟨892553639832693353880977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380143039553848943682605 892553639832693353880977)
                      ·
                        rfl

theorem cell23_1738242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1738242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738242 prefixEnd_1738242 := by exact prefixLift 1738242
  have htrace : WordTrace (prefixWord ++ tailWord_1738242) baseStart_1738242 baseEnd_1738242 := by
    simpa [prefixWord, tailWord_1738242, baseEnd_1738242] using wordTrace_append hprefix tailTrace_1738242
  have hstable : (prefixWord ++ tailWord_1738242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738242).length < 2 ^ (prefixWord ++ tailWord_1738242).sum := by decide
  have hdescent : baseEnd_1738242 < baseStart_1738242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738272 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1738272 : Nat := 118140960795 + 1738272 * 2 ^ 59
def prefixEnd_1738272 : Nat := 4983230072969 + 3 ^ 40 * 1738272 * 2
def baseEnd_1738272 : Nat := 892569044252328236505839

theorem tailTrace_1738272 : CollatzResearch.WordTrace tailWord_1738272 prefixEnd_1738272 892569044252328236505839 := by
  unfold tailWord_1738272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699994179272446033712535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42266658905696594711616713 31699994179272446033712535)
  ·
    refine ⟨47549991268908669050568803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31699994179272446033712535 47549991268908669050568803)
    ·
      refine ⟨71324986903363003575853205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47549991268908669050568803 71324986903363003575853205)
      ·
        refine ⟨3343358761095140792618119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71324986903363003575853205 3343358761095140792618119)
        ·
          refine ⟨5015038141642711188927179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343358761095140792618119 5015038141642711188927179)
          ·
            refine ⟨7522557212464066783390769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015038141642711188927179 7522557212464066783390769)
            ·
              refine ⟨5641917909348050087543077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7522557212464066783390769 5641917909348050087543077)
              ·
                refine ⟨1057859608002759391414327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5641917909348050087543077 1057859608002759391414327)
                ·
                  refine ⟨1586789412004139087121491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057859608002759391414327 1586789412004139087121491)
                  ·
                    refine ⟨2380184118006208630682237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586789412004139087121491 2380184118006208630682237)
                    ·
                      refine ⟨892569044252328236505839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380184118006208630682237 892569044252328236505839)
                      ·
                        rfl

theorem cell23_1738272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1738272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738272 prefixEnd_1738272 := by exact prefixLift 1738272
  have htrace : WordTrace (prefixWord ++ tailWord_1738272) baseStart_1738272 baseEnd_1738272 := by
    simpa [prefixWord, tailWord_1738272, baseEnd_1738272] using wordTrace_append hprefix tailTrace_1738272
  have hstable : (prefixWord ++ tailWord_1738272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738272).length < 2 ^ (prefixWord ++ tailWord_1738272).sum := by decide
  have hdescent : baseEnd_1738272 < baseStart_1738272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738291 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_1738291 : Nat := 118140960795 + 1738291 * 2 ^ 59
def prefixEnd_1738291 : Nat := 4983230072969 + 3 ^ 40 * 1738291 * 2
def baseEnd_1738291 : Nat := 892578800384763662168251

theorem tailTrace_1738291 : CollatzResearch.WordTrace tailWord_1738291 prefixEnd_1738291 892578800384763662168251 := by
  unfold tailWord_1738291
  simp only [CollatzResearch.WordTrace]
  refine ⟨63400681345476058312366727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42267120896984038874911151 63400681345476058312366727)
  ·
    refine ⟨95101022018214087468550091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63400681345476058312366727 95101022018214087468550091)
    ·
      refine ⟨142651533027321131202825137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95101022018214087468550091 142651533027321131202825137)
      ·
        refine ⟨106988649770490848402118853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142651533027321131202825137 106988649770490848402118853)
        ·
          refine ⟨20060371831967034075397285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106988649770490848402118853 20060371831967034075397285)
          ·
            refine ⟨3761319718493818889136991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20060371831967034075397285 3761319718493818889136991)
            ·
              refine ⟨5641979577740728333705487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761319718493818889136991 5641979577740728333705487)
              ·
                refine ⟨8462969366611092500558231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641979577740728333705487 8462969366611092500558231)
                ·
                  refine ⟨12694454049916638750837347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8462969366611092500558231 12694454049916638750837347)
                  ·
                    refine ⟨19041681074874958126256021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12694454049916638750837347 19041681074874958126256021)
                    ·
                      refine ⟨892578800384763662168251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19041681074874958126256021 892578800384763662168251)
                      ·
                        rfl

theorem cell23_1738291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_1738291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738291 prefixEnd_1738291 := by exact prefixLift 1738291
  have htrace : WordTrace (prefixWord ++ tailWord_1738291) baseStart_1738291 baseEnd_1738291 := by
    simpa [prefixWord, tailWord_1738291, baseEnd_1738291] using wordTrace_append hprefix tailTrace_1738291
  have hstable : (prefixWord ++ tailWord_1738291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738291).length < 2 ^ (prefixWord ++ tailWord_1738291).sum := by decide
  have hdescent : baseEnd_1738291 < baseStart_1738291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738295 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_1738295 : Nat := 118140960795 + 1738295 * 2 ^ 59
def prefixEnd_1738295 : Nat := 4983230072969 + 3 ^ 40 * 1738295 * 2
def baseEnd_1738295 : Nat := 892580854307381646518233

theorem tailTrace_1738295 : CollatzResearch.WordTrace tailWord_1738295 prefixEnd_1738295 892580854307381646518233 := by
  unfold tailWord_1738295
  simp only [CollatzResearch.WordTrace]
  refine ⟨63400827237461566995512339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42267218158307711330341559 63400827237461566995512339)
  ·
    refine ⟨95101240856192350493268509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63400827237461566995512339 95101240856192350493268509)
    ·
      refine ⟨35662965321072131434975691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95101240856192350493268509 35662965321072131434975691)
      ·
        refine ⟨53494447981608197152463537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35662965321072131434975691 53494447981608197152463537)
        ·
          refine ⟨40120835986206147864347653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53494447981608197152463537 40120835986206147864347653)
          ·
            refine ⟨7522656747413652724565185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40120835986206147864347653 7522656747413652724565185)
            ·
              refine ⟨5641992560560239543423889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7522656747413652724565185 5641992560560239543423889)
              ·
                refine ⟨4231494420420179657567917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641992560560239543423889 4231494420420179657567917)
                ·
                  refine ⟨1586810407657567371587969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4231494420420179657567917 1586810407657567371587969)
                  ·
                    refine ⟨1190107805743175528690977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586810407657567371587969 1190107805743175528690977)
                    ·
                      refine ⟨892580854307381646518233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190107805743175528690977 892580854307381646518233)
                      ·
                        rfl

theorem cell23_1738295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_1738295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738295 prefixEnd_1738295 := by exact prefixLift 1738295
  have htrace : WordTrace (prefixWord ++ tailWord_1738295) baseStart_1738295 baseEnd_1738295 := by
    simpa [prefixWord, tailWord_1738295, baseEnd_1738295] using wordTrace_append hprefix tailTrace_1738295
  have hstable : (prefixWord ++ tailWord_1738295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738295).length < 2 ^ (prefixWord ++ tailWord_1738295).sum := by decide
  have hdescent : baseEnd_1738295 < baseStart_1738295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738349 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1738349 : Nat := 118140960795 + 1738349 * 2 ^ 59
def prefixEnd_1738349 : Nat := 4983230072969 + 3 ^ 40 * 1738349 * 2
def baseEnd_1738349 : Nat := 892608582262724435242985

theorem tailTrace_1738349 : CollatzResearch.WordTrace tailWord_1738349 prefixEnd_1738349 892608582262724435242985 := by
  unfold tailWord_1738349
  simp only [CollatzResearch.WordTrace]
  refine ⟨63402796779265934217978101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42268531186177289478652067 63402796779265934217978101)
  ·
    refine ⟨5944012198056181332935447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63402796779265934217978101 5944012198056181332935447)
    ·
      refine ⟨8916018297084271999403171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5944012198056181332935447 8916018297084271999403171)
      ·
        refine ⟨13374027445626407999104757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916018297084271999403171 13374027445626407999104757)
        ·
          refine ⟨1253815073027475749916071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13374027445626407999104757 1253815073027475749916071)
          ·
            refine ⟨1880722609541213624874107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253815073027475749916071 1880722609541213624874107)
            ·
              refine ⟨2821083914311820437311161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880722609541213624874107 2821083914311820437311161)
              ·
                refine ⟨2115812935733865327983371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821083914311820437311161 2115812935733865327983371)
                ·
                  refine ⟨3173719403600797991975057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115812935733865327983371 3173719403600797991975057)
                  ·
                    refine ⟨2380289552700598493981293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173719403600797991975057 2380289552700598493981293)
                    ·
                      refine ⟨892608582262724435242985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380289552700598493981293 892608582262724435242985)
                      ·
                        rfl

theorem cell23_1738349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1738349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738349 prefixEnd_1738349 := by exact prefixLift 1738349
  have htrace : WordTrace (prefixWord ++ tailWord_1738349) baseStart_1738349 baseEnd_1738349 := by
    simpa [prefixWord, tailWord_1738349, baseEnd_1738349] using wordTrace_append hprefix tailTrace_1738349
  have hstable : (prefixWord ++ tailWord_1738349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738349).length < 2 ^ (prefixWord ++ tailWord_1738349).sum := by decide
  have hdescent : baseEnd_1738349 < baseStart_1738349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738458 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1738458 : Nat := 118140960795 + 1738458 * 2 ^ 59
def prefixEnd_1738458 : Nat := 4983230072969 + 3 ^ 40 * 1738458 * 2
def baseEnd_1738458 : Nat := 892664551654064508779983

theorem tailTrace_1738458 : CollatzResearch.WordTrace tailWord_1738458 prefixEnd_1738458 892664551654064508779983 := by
  unfold tailWord_1738458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851693083967761458424007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42271181557247363889130685 15851693083967761458424007)
  ·
    refine ⟨23777539625951642187636011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15851693083967761458424007 23777539625951642187636011)
    ·
      refine ⟨35666309438927463281454017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23777539625951642187636011 35666309438927463281454017)
      ·
        refine ⟨26749732079195597461090513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35666309438927463281454017 26749732079195597461090513)
        ·
          refine ⟨20062299059396698095817885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26749732079195597461090513 20062299059396698095817885)
          ·
            refine ⟨7523362147273761785931707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20062299059396698095817885 7523362147273761785931707)
            ·
              refine ⟨11285043220910642678897561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523362147273761785931707 11285043220910642678897561)
              ·
                refine ⟨8463782415682982009173171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11285043220910642678897561 8463782415682982009173171)
                ·
                  refine ⟨12695673623524473013759757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8463782415682982009173171 12695673623524473013759757)
                  ·
                    refine ⟨4760877608821677380159909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12695673623524473013759757 4760877608821677380159909)
                    ·
                      refine ⟨892664551654064508779983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4760877608821677380159909 892664551654064508779983)
                      ·
                        rfl

theorem cell23_1738458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1738458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738458 prefixEnd_1738458 := by exact prefixLift 1738458
  have htrace : WordTrace (prefixWord ++ tailWord_1738458) baseStart_1738458 baseEnd_1738458 := by
    simpa [prefixWord, tailWord_1738458, baseEnd_1738458] using wordTrace_append hprefix tailTrace_1738458
  have hstable : (prefixWord ++ tailWord_1738458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738458).length < 2 ^ (prefixWord ++ tailWord_1738458).sum := by decide
  have hdescent : baseEnd_1738458 < baseStart_1738458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738526 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1738526 : Nat := 118140960795 + 1738526 * 2 ^ 59
def prefixEnd_1738526 : Nat := 4983230072969 + 3 ^ 40 * 1738526 * 2
def baseEnd_1738526 : Nat := 892699468338570242729671

theorem tailTrace_1738526 : CollatzResearch.WordTrace tailWord_1738526 prefixEnd_1738526 892699468338570242729671 := by
  unfold tailWord_1738526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926156562453086680896429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42272834999749795631447621 7926156562453086680896429)
  ·
    refine ⟨2972308710919907505336161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7926156562453086680896429 2972308710919907505336161)
    ·
      refine ⟨2229231533189930629002121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972308710919907505336161 2229231533189930629002121)
      ·
        refine ⟨1671923649892447971751591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229231533189930629002121 1671923649892447971751591)
        ·
          refine ⟨2507885474838671957627387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671923649892447971751591 2507885474838671957627387)
          ·
            refine ⟨3761828212258007936441081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507885474838671957627387 3761828212258007936441081)
            ·
              refine ⟨2821371159193505952330811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761828212258007936441081 2821371159193505952330811)
              ·
                refine ⟨4232056738790258928496217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821371159193505952330811 4232056738790258928496217)
                ·
                  refine ⟨3174042554092694196372163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232056738790258928496217 3174042554092694196372163)
                  ·
                    refine ⟨4761063831139041294558245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174042554092694196372163 4761063831139041294558245)
                    ·
                      refine ⟨892699468338570242729671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4761063831139041294558245 892699468338570242729671)
                      ·
                        rfl

theorem cell23_1738526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1738526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738526 prefixEnd_1738526 := by exact prefixLift 1738526
  have htrace : WordTrace (prefixWord ++ tailWord_1738526) baseStart_1738526 baseEnd_1738526 := by
    simpa [prefixWord, tailWord_1738526, baseEnd_1738526] using wordTrace_append hprefix tailTrace_1738526
  have hstable : (prefixWord ++ tailWord_1738526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738526).length < 2 ^ (prefixWord ++ tailWord_1738526).sum := by decide
  have hdescent : baseEnd_1738526 < baseStart_1738526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738552 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_1738552 : Nat := 118140960795 + 1738552 * 2 ^ 59
def prefixEnd_1738552 : Nat := 4983230072969 + 3 ^ 40 * 1738552 * 2
def baseEnd_1738552 : Nat := 892712818835587141004551

theorem tailTrace_1738552 : CollatzResearch.WordTrace tailWord_1738552 prefixEnd_1738552 892712818835587141004551 := by
  unfold tailWord_1738552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31705100398765249943808955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42273467198353666591745273 31705100398765249943808955)
  ·
    refine ⟨47557650598147874915713433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31705100398765249943808955 47557650598147874915713433)
    ·
      refine ⟨35668237948610906186785075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47557650598147874915713433 35668237948610906186785075)
      ·
        refine ⟨53502356922916359280177613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35668237948610906186785075 53502356922916359280177613)
        ·
          refine ⟨20063383846093634730066605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53502356922916359280177613 20063383846093634730066605)
          ·
            refine ⟨7523768942285113023774977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20063383846093634730066605 7523768942285113023774977)
            ·
              refine ⟨5642826706713834767831233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7523768942285113023774977 5642826706713834767831233)
              ·
                refine ⟨4232120030035376075873425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642826706713834767831233 4232120030035376075873425)
                ·
                  refine ⟨3174090022526532056905069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232120030035376075873425 3174090022526532056905069)
                  ·
                    refine ⟨1190283758447449521339401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174090022526532056905069 1190283758447449521339401)
                    ·
                      refine ⟨892712818835587141004551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190283758447449521339401 892712818835587141004551)
                      ·
                        rfl

theorem cell23_1738552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_1738552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738552 prefixEnd_1738552 := by exact prefixLift 1738552
  have htrace : WordTrace (prefixWord ++ tailWord_1738552) baseStart_1738552 baseEnd_1738552 := by
    simpa [prefixWord, tailWord_1738552, baseEnd_1738552] using wordTrace_append hprefix tailTrace_1738552
  have hstable : (prefixWord ++ tailWord_1738552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738552).length < 2 ^ (prefixWord ++ tailWord_1738552).sum := by decide
  have hdescent : baseEnd_1738552 < baseStart_1738552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738553 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 1, 4]
def baseStart_1738553 : Nat := 118140960795 + 1738553 * 2 ^ 59
def prefixEnd_1738553 : Nat := 4983230072969 + 3 ^ 40 * 1738553 * 2
def baseEnd_1738553 : Nat := 297571110772080545697349

theorem tailTrace_1738553 : CollatzResearch.WordTrace tailWord_1738553 prefixEnd_1738553 297571110772080545697349 := by
  unfold tailWord_1738553
  simp only [CollatzResearch.WordTrace]
  refine ⟨63410237270526877058404313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42273491513684584705602875 63410237270526877058404313)
  ·
    refine ⟨47557677952895157793803235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63410237270526877058404313 47557677952895157793803235)
    ·
      refine ⟨71336516929342736690704853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47557677952895157793803235 71336516929342736690704853)
      ·
        refine ⟨1671949615531470391188395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 71336516929342736690704853 1671949615531470391188395)
        ·
          refine ⟨2507924423297205586782593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671949615531470391188395 2507924423297205586782593)
          ·
            refine ⟨1880943317472904190086945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507924423297205586782593 1880943317472904190086945)
            ·
              refine ⟨1410707488104678142565209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880943317472904190086945 1410707488104678142565209)
              ·
                refine ⟨1058030616078508606923907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410707488104678142565209 1058030616078508606923907)
                ·
                  refine ⟨1587045924117762910385861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058030616078508606923907 1587045924117762910385861)
                  ·
                    refine ⟨297571110772080545697349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587045924117762910385861 297571110772080545697349)
                    ·
                      rfl

theorem cell23_1738553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_1738553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738553 prefixEnd_1738553 := by exact prefixLift 1738553
  have htrace : WordTrace (prefixWord ++ tailWord_1738553) baseStart_1738553 baseEnd_1738553 := by
    simpa [prefixWord, tailWord_1738553, baseEnd_1738553] using wordTrace_append hprefix tailTrace_1738553
  have hstable : (prefixWord ++ tailWord_1738553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738553).length < 2 ^ (prefixWord ++ tailWord_1738553).sum := by decide
  have hdescent : baseEnd_1738553 < baseStart_1738553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738585 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_1738585 : Nat := 118140960795 + 1738585 * 2 ^ 59
def prefixEnd_1738585 : Nat := 4983230072969 + 3 ^ 40 * 1738585 * 2
def baseEnd_1738585 : Nat := 892729763697185511891899

theorem tailTrace_1738585 : CollatzResearch.WordTrace tailWord_1738585 prefixEnd_1738585 892729763697185511891899 := by
  unfold tailWord_1738585
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411404406410946523569209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42274269604273964349046139 63411404406410946523569209)
  ·
    refine ⟨47558553304808209892676907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63411404406410946523569209 47558553304808209892676907)
    ·
      refine ⟨71337829957212314839015361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47558553304808209892676907 71337829957212314839015361)
      ·
        refine ⟨53503372467909236129261521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71337829957212314839015361 53503372467909236129261521)
        ·
          refine ⟨40127529350931927096946141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53503372467909236129261521 40127529350931927096946141)
          ·
            refine ⟨15047823506599472661354803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40127529350931927096946141 15047823506599472661354803)
            ·
              refine ⟨22571735259899208992032205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15047823506599472661354803 22571735259899208992032205)
              ·
                refine ⟨8464400722462203372012077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22571735259899208992032205 8464400722462203372012077)
                ·
                  refine ⟨3174150270923326264504529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8464400722462203372012077 3174150270923326264504529)
                  ·
                    refine ⟨2380612703192494698378397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174150270923326264504529 2380612703192494698378397)
                    ·
                      refine ⟨892729763697185511891899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380612703192494698378397 892729763697185511891899)
                      ·
                        rfl

theorem cell23_1738585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_1738585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738585 prefixEnd_1738585 := by exact prefixLift 1738585
  have htrace : WordTrace (prefixWord ++ tailWord_1738585) baseStart_1738585 baseEnd_1738585 := by
    simpa [prefixWord, tailWord_1738585, baseEnd_1738585] using wordTrace_append hprefix tailTrace_1738585
  have hstable : (prefixWord ++ tailWord_1738585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738585).length < 2 ^ (prefixWord ++ tailWord_1738585).sum := by decide
  have hdescent : baseEnd_1738585 < baseStart_1738585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738596 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1738596 : Nat := 118140960795 + 1738596 * 2 ^ 59
def prefixEnd_1738596 : Nat := 4983230072969 + 3 ^ 40 * 1738596 * 2
def baseEnd_1738596 : Nat := 297578470661461656284783

theorem tailTrace_1738596 : CollatzResearch.WordTrace tailWord_1738596 prefixEnd_1738596 297578470661461656284783 := by
  unfold tailWord_1738596
  simp only [CollatzResearch.WordTrace]
  refine ⟨31705902804685547701109821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42274537072914063601479761 31705902804685547701109821)
  ·
    refine ⟨11889713551757080387916183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31705902804685547701109821 11889713551757080387916183)
    ·
      refine ⟨17834570327635620581874275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11889713551757080387916183 17834570327635620581874275)
      ·
        refine ⟨26751855491453430872811413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17834570327635620581874275 26751855491453430872811413)
        ·
          refine ⟨1253993226161879572163035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26751855491453430872811413 1253993226161879572163035)
          ·
            refine ⟨1880989839242819358244553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253993226161879572163035 1880989839242819358244553)
            ·
              refine ⟨1410742379432114518683415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880989839242819358244553 1410742379432114518683415)
              ·
                refine ⟨2116113569148171778025123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410742379432114518683415 2116113569148171778025123)
                ·
                  refine ⟨3174170353722257667037685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116113569148171778025123 3174170353722257667037685)
                  ·
                    refine ⟨297578470661461656284783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3174170353722257667037685 297578470661461656284783)
                    ·
                      rfl

theorem cell23_1738596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1738596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738596 prefixEnd_1738596 := by exact prefixLift 1738596
  have htrace : WordTrace (prefixWord ++ tailWord_1738596) baseStart_1738596 baseEnd_1738596 := by
    simpa [prefixWord, tailWord_1738596, baseEnd_1738596] using wordTrace_append hprefix tailTrace_1738596
  have hstable : (prefixWord ++ tailWord_1738596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738596).length < 2 ^ (prefixWord ++ tailWord_1738596).sum := by decide
  have hdescent : baseEnd_1738596 < baseStart_1738596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1738608 : Nat := 118140960795 + 1738608 * 2 ^ 59
def prefixEnd_1738608 : Nat := 4983230072969 + 3 ^ 40 * 1738608 * 2
def baseEnd_1738608 : Nat := 892741573752238921904293

theorem tailTrace_1738608 : CollatzResearch.WordTrace tailWord_1738608 prefixEnd_1738608 892741573752238921904293 := by
  unfold tailWord_1738608
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706121642663810725828239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42274828856885080967770985 31706121642663810725828239)
  ·
    refine ⟨47559182463995716088742359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31706121642663810725828239 47559182463995716088742359)
    ·
      refine ⟨71338773695993574133113539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47559182463995716088742359 71338773695993574133113539)
      ·
        refine ⟨107008160543990361199670309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71338773695993574133113539 107008160543990361199670309)
        ·
          refine ⟨20064030101998192724938183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107008160543990361199670309 20064030101998192724938183)
          ·
            refine ⟨30096045152997289087407275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20064030101998192724938183 30096045152997289087407275)
            ·
              refine ⟨45144067729495933631110913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30096045152997289087407275 45144067729495933631110913)
              ·
                refine ⟨33858050797121950223333185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45144067729495933631110913 33858050797121950223333185)
                ·
                  refine ⟨25393538097841462667499889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33858050797121950223333185 25393538097841462667499889)
                  ·
                    refine ⟨19045153573381097000624917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25393538097841462667499889 19045153573381097000624917)
                    ·
                      refine ⟨892741573752238921904293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19045153573381097000624917 892741573752238921904293)
                      ·
                        rfl

theorem cell23_1738608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1738608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738608 prefixEnd_1738608 := by exact prefixLift 1738608
  have htrace : WordTrace (prefixWord ++ tailWord_1738608) baseStart_1738608 baseEnd_1738608 := by
    simpa [prefixWord, tailWord_1738608, baseEnd_1738608] using wordTrace_append hprefix tailTrace_1738608
  have hstable : (prefixWord ++ tailWord_1738608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738608).length < 2 ^ (prefixWord ++ tailWord_1738608).sum := by decide
  have hdescent : baseEnd_1738608 < baseStart_1738608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738618 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1738618 : Nat := 118140960795 + 1738618 * 2 ^ 59
def prefixEnd_1738618 : Nat := 4983230072969 + 3 ^ 40 * 1738618 * 2
def baseEnd_1738618 : Nat := 297582236186261294259749

theorem tailTrace_1738618 : CollatzResearch.WordTrace tailWord_1738618 prefixEnd_1738618 297582236186261294259749 := by
  unfold tailWord_1738618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853152003822848289880127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42275072010194262106347005 15853152003822848289880127)
  ·
    refine ⟨23779728005734272434820191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15853152003822848289880127 23779728005734272434820191)
    ·
      refine ⟨35669592008601408652230287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779728005734272434820191 35669592008601408652230287)
      ·
        refine ⟨53504388012902112978345431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35669592008601408652230287 53504388012902112978345431)
        ·
          refine ⟨80256582019353169467518147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53504388012902112978345431 80256582019353169467518147)
          ·
            refine ⟨120384873029029754201277221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80256582019353169467518147 120384873029029754201277221)
            ·
              refine ⟨22572163692943078912739479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120384873029029754201277221 22572163692943078912739479)
              ·
                refine ⟨33858245539414618369109219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22572163692943078912739479 33858245539414618369109219)
                ·
                  refine ⟨50787368309121927553663829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33858245539414618369109219 50787368309121927553663829)
                  ·
                    refine ⟨297582236186261294259749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50787368309121927553663829 297582236186261294259749)
                    ·
                      rfl

theorem cell23_1738618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1738618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738618 prefixEnd_1738618 := by exact prefixLift 1738618
  have htrace : WordTrace (prefixWord ++ tailWord_1738618) baseStart_1738618 baseEnd_1738618 := by
    simpa [prefixWord, tailWord_1738618, baseEnd_1738618] using wordTrace_append hprefix tailTrace_1738618
  have hstable : (prefixWord ++ tailWord_1738618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738618).length < 2 ^ (prefixWord ++ tailWord_1738618).sum := by decide
  have hdescent : baseEnd_1738618 < baseStart_1738618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738675 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3]
def baseStart_1738675 : Nat := 118140960795 + 1738675 * 2 ^ 59
def prefixEnd_1738675 : Nat := 4983230072969 + 3 ^ 40 * 1738675 * 2
def baseEnd_1738675 : Nat := 892775976956090159766485

theorem tailTrace_1738675 : CollatzResearch.WordTrace tailWord_1738675 prefixEnd_1738675 892775976956090159766485 := by
  unfold tailWord_1738675
  simp only [CollatzResearch.WordTrace]
  refine ⟨63414686976084891894345479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42276457984056594596230319 63414686976084891894345479)
  ·
    refine ⟨95122030464127337841518219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63414686976084891894345479 95122030464127337841518219)
    ·
      refine ⟨142683045696191006762277329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95122030464127337841518219 142683045696191006762277329)
      ·
        refine ⟨107012284272143255071707997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142683045696191006762277329 107012284272143255071707997)
        ·
          refine ⟨40129606602053720651890499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107012284272143255071707997 40129606602053720651890499)
          ·
            refine ⟨60194409903080580977835749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40129606602053720651890499 60194409903080580977835749)
            ·
              refine ⟨11286451856827608933344203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60194409903080580977835749 11286451856827608933344203)
              ·
                refine ⟨16929677785241413400016305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286451856827608933344203 16929677785241413400016305)
                ·
                  refine ⟨12697258338931060050012229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16929677785241413400016305 12697258338931060050012229)
                  ·
                    refine ⟨2380735938549573759377293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12697258338931060050012229 2380735938549573759377293)
                    ·
                      refine ⟨892775976956090159766485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380735938549573759377293 892775976956090159766485)
                      ·
                        rfl

theorem cell23_1738675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_1738675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738675 prefixEnd_1738675 := by exact prefixLift 1738675
  have htrace : WordTrace (prefixWord ++ tailWord_1738675) baseStart_1738675 baseEnd_1738675 := by
    simpa [prefixWord, tailWord_1738675, baseEnd_1738675] using wordTrace_append hprefix tailTrace_1738675
  have hstable : (prefixWord ++ tailWord_1738675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738675).length < 2 ^ (prefixWord ++ tailWord_1738675).sum := by decide
  have hdescent : baseEnd_1738675 < baseStart_1738675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738705 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_1738705 : Nat := 118140960795 + 1738705 * 2 ^ 59
def prefixEnd_1738705 : Nat := 4983230072969 + 3 ^ 40 * 1738705 * 2
def baseEnd_1738705 : Nat := 892791381375725042391347

theorem tailTrace_1738705 : CollatzResearch.WordTrace tailWord_1738705 prefixEnd_1738705 892791381375725042391347 := by
  unfold tailWord_1738705
  simp only [CollatzResearch.WordTrace]
  refine ⟨63415781165976207017937569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42277187443984138011958379 63415781165976207017937569)
  ·
    refine ⟨47561835874482155263453177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63415781165976207017937569 47561835874482155263453177)
    ·
      refine ⟨35671376905861616447589883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47561835874482155263453177 35671376905861616447589883)
      ·
        refine ⟨53507065358792424671384825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35671376905861616447589883 53507065358792424671384825)
        ·
          refine ⟨40130299019094318503538619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53507065358792424671384825 40130299019094318503538619)
          ·
            refine ⟨60195448528641477755307929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40130299019094318503538619 60195448528641477755307929)
            ·
              refine ⟨45146586396481108316480947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60195448528641477755307929 45146586396481108316480947)
              ·
                refine ⟨67719879594721662474721421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45146586396481108316480947 67719879594721662474721421)
                ·
                  refine ⟨25394954848020623428020533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67719879594721662474721421 25394954848020623428020533)
                  ·
                    refine ⟨2380777017001933446376925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25394954848020623428020533 2380777017001933446376925)
                    ·
                      refine ⟨892791381375725042391347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380777017001933446376925 892791381375725042391347)
                      ·
                        rfl

theorem cell23_1738705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_1738705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738705 prefixEnd_1738705 := by exact prefixLift 1738705
  have htrace : WordTrace (prefixWord ++ tailWord_1738705) baseStart_1738705 baseEnd_1738705 := by
    simpa [prefixWord, tailWord_1738705, baseEnd_1738705] using wordTrace_append hprefix tailTrace_1738705
  have hstable : (prefixWord ++ tailWord_1738705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738705).length < 2 ^ (prefixWord ++ tailWord_1738705).sum := by decide
  have hdescent : baseEnd_1738705 < baseStart_1738705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738706 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1738706 : Nat := 118140960795 + 1738706 * 2 ^ 59
def prefixEnd_1738706 : Nat := 4983230072969 + 3 ^ 40 * 1738706 * 2
def baseEnd_1738706 : Nat := 892791894856379538478843

theorem tailTrace_1738706 : CollatzResearch.WordTrace tailWord_1738706 prefixEnd_1738706 892791894856379538478843 := by
  unfold tailWord_1738706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853954409743146047180993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42277211759315056125815981 15853954409743146047180993)
  ·
    refine ⟨11890465807307359535385745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15853954409743146047180993 11890465807307359535385745)
    ·
      refine ⟨8917849355480519651539309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890465807307359535385745 8917849355480519651539309)
      ·
        refine ⟨3344193508305194869327241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8917849355480519651539309 3344193508305194869327241)
        ·
          refine ⟨2508145131228896151995431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344193508305194869327241 2508145131228896151995431)
          ·
            refine ⟨3762217696843344227993147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508145131228896151995431 3762217696843344227993147)
            ·
              refine ⟨5643326545265016341989721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762217696843344227993147 5643326545265016341989721)
              ·
                refine ⟨4232494908948762256492291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643326545265016341989721 4232494908948762256492291)
                ·
                  refine ⟨6348742363423143384738437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232494908948762256492291 6348742363423143384738437)
                  ·
                    refine ⟨1190389193141839384638457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348742363423143384738437 1190389193141839384638457)
                    ·
                      refine ⟨892791894856379538478843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190389193141839384638457 892791894856379538478843)
                      ·
                        rfl

theorem cell23_1738706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1738706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738706 prefixEnd_1738706 := by exact prefixLift 1738706
  have htrace : WordTrace (prefixWord ++ tailWord_1738706) baseStart_1738706 baseEnd_1738706 := by
    simpa [prefixWord, tailWord_1738706, baseEnd_1738706] using wordTrace_append hprefix tailTrace_1738706
  have hstable : (prefixWord ++ tailWord_1738706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738706).length < 2 ^ (prefixWord ++ tailWord_1738706).sum := by decide
  have hdescent : baseEnd_1738706 < baseStart_1738706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738710 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1738710 : Nat := 118140960795 + 1738710 * 2 ^ 59
def prefixEnd_1738710 : Nat := 4983230072969 + 3 ^ 40 * 1738710 * 2
def baseEnd_1738710 : Nat := 892793948778997522828825

theorem tailTrace_1738710 : CollatzResearch.WordTrace tailWord_1738710 prefixEnd_1738710 892793948778997522828825 := by
  unfold tailWord_1738710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963497720684880804491849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42277309020638728581246389 3963497720684880804491849)
  ·
    refine ⟨2972623290513660603368887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3963497720684880804491849 2972623290513660603368887)
    ·
      refine ⟨4458934935770490905053331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972623290513660603368887 4458934935770490905053331)
      ·
        refine ⟨6688402403655736357579997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458934935770490905053331 6688402403655736357579997)
        ·
          refine ⟨2508150901370901134092499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6688402403655736357579997 2508150901370901134092499)
          ·
            refine ⟨3762226352056351701138749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508150901370901134092499 3762226352056351701138749)
            ·
              refine ⟨1410834882021131887927031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762226352056351701138749 1410834882021131887927031)
              ·
                refine ⟨2116252323031697831890547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410834882021131887927031 2116252323031697831890547)
                ·
                  refine ⟨3174378484547546747835821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116252323031697831890547 3174378484547546747835821)
                  ·
                    refine ⟨1190391931705330030438433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174378484547546747835821 1190391931705330030438433)
                    ·
                      refine ⟨892793948778997522828825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190391931705330030438433 892793948778997522828825)
                      ·
                        rfl

theorem cell23_1738710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1738710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738710 prefixEnd_1738710 := by exact prefixLift 1738710
  have htrace : WordTrace (prefixWord ++ tailWord_1738710) baseStart_1738710 baseEnd_1738710 := by
    simpa [prefixWord, tailWord_1738710, baseEnd_1738710] using wordTrace_append hprefix tailTrace_1738710
  have hstable : (prefixWord ++ tailWord_1738710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738710).length < 2 ^ (prefixWord ++ tailWord_1738710).sum := by decide
  have hdescent : baseEnd_1738710 < baseStart_1738710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738712 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 5]
def baseStart_1738712 : Nat := 118140960795 + 1738712 * 2 ^ 59
def prefixEnd_1738712 : Nat := 4983230072969 + 3 ^ 40 * 1738712 * 2
def baseEnd_1738712 : Nat := 99199441748922946111535

theorem tailTrace_1738712 : CollatzResearch.WordTrace tailWord_1738712 prefixEnd_1738712 99199441748922946111535 := by
  unfold tailWord_1738712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708018238475423606721195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42277357651300564808961593 31708018238475423606721195)
  ·
    refine ⟨47562027357713135410081793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31708018238475423606721195 47562027357713135410081793)
    ·
      refine ⟨35671520518284851557561345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47562027357713135410081793 35671520518284851557561345)
      ·
        refine ⟨26753640388713638668171009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35671520518284851557561345 26753640388713638668171009)
        ·
          refine ⟨20065230291535229001128257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26753640388713638668171009 20065230291535229001128257)
          ·
            refine ⟨15048922718651421750846193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20065230291535229001128257 15048922718651421750846193)
            ·
              refine ⟨11286692038988566313134645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15048922718651421750846193 11286692038988566313134645)
              ·
                refine ⟨1058127378655178091856373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11286692038988566313134645 1058127378655178091856373)
                ·
                  refine ⟨99199441748922946111535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1058127378655178091856373 99199441748922946111535)
                  ·
                    rfl

theorem cell23_1738712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 5].length) (baseStart_1738712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738712 prefixEnd_1738712 := by exact prefixLift 1738712
  have htrace : WordTrace (prefixWord ++ tailWord_1738712) baseStart_1738712 baseEnd_1738712 := by
    simpa [prefixWord, tailWord_1738712, baseEnd_1738712] using wordTrace_append hprefix tailTrace_1738712
  have hstable : (prefixWord ++ tailWord_1738712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738712).length < 2 ^ (prefixWord ++ tailWord_1738712).sum := by decide
  have hdescent : baseEnd_1738712 < baseStart_1738712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738735 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_1738735 : Nat := 118140960795 + 1738735 * 2 ^ 59
def prefixEnd_1738735 : Nat := 4983230072969 + 3 ^ 40 * 1738735 * 2
def baseEnd_1738735 : Nat := 892806785795359925016209

theorem tailTrace_1738735 : CollatzResearch.WordTrace tailWord_1738735 prefixEnd_1738735 892806785795359925016209 := by
  unfold tailWord_1738735
  simp only [CollatzResearch.WordTrace]
  refine ⟨63416875355867522141529659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42277916903911681427686439 63416875355867522141529659)
  ·
    refine ⟨95125313033801283212294489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63416875355867522141529659 95125313033801283212294489)
    ·
      refine ⟨71343984775350962409220867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95125313033801283212294489 71343984775350962409220867)
      ·
        refine ⟨107015977163026443613831301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71343984775350962409220867 107015977163026443613831301)
        ·
          refine ⟨20065495718067458177593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107015977163026443613831301 20065495718067458177593369)
          ·
            refine ⟨15049121788550593633195027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20065495718067458177593369 15049121788550593633195027)
            ·
              refine ⟨22573682682825890449792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049121788550593633195027 22573682682825890449792541)
              ·
                refine ⟨8465131006059708918672203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22573682682825890449792541 8465131006059708918672203)
                ·
                  refine ⟨12697696509089563378008305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465131006059708918672203 12697696509089563378008305)
                  ·
                    refine ⟨9523272381817172533506229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12697696509089563378008305 9523272381817172533506229)
                    ·
                      refine ⟨892806785795359925016209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9523272381817172533506229 892806785795359925016209)
                      ·
                        rfl

theorem cell23_1738735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_1738735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738735 prefixEnd_1738735 := by exact prefixLift 1738735
  have htrace : WordTrace (prefixWord ++ tailWord_1738735) baseStart_1738735 baseEnd_1738735 := by
    simpa [prefixWord, tailWord_1738735, baseEnd_1738735] using wordTrace_append hprefix tailTrace_1738735
  have hstable : (prefixWord ++ tailWord_1738735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738735).length < 2 ^ (prefixWord ++ tailWord_1738735).sum := by decide
  have hdescent : baseEnd_1738735 < baseStart_1738735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738759 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1738759 : Nat := 118140960795 + 1738759 * 2 ^ 59
def prefixEnd_1738759 : Nat := 4983230072969 + 3 ^ 40 * 1738759 * 2
def baseEnd_1738759 : Nat := 297606369777022610372033

theorem tailTrace_1738759 : CollatzResearch.WordTrace tailWord_1738759 prefixEnd_1738759 297606369777022610372033 := by
  unfold tailWord_1738759
  simp only [CollatzResearch.WordTrace]
  refine ⟨63417750707780574240403331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42278500471853716160268887 63417750707780574240403331)
  ·
    refine ⟨95126626061670861360604997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63417750707780574240403331 95126626061670861360604997)
    ·
      refine ⟨17836242386563286505113437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95126626061670861360604997 17836242386563286505113437)
      ·
        refine ⟨6688590894961232439417539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17836242386563286505113437 6688590894961232439417539)
        ·
          refine ⟨10032886342441848659126309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688590894961232439417539 10032886342441848659126309)
          ·
            refine ⟨1881166189207846623586183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10032886342441848659126309 1881166189207846623586183)
            ·
              refine ⟨2821749283811769935379275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881166189207846623586183 2821749283811769935379275)
              ·
                refine ⟨4232623925717654903068913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821749283811769935379275 4232623925717654903068913)
                ·
                  refine ⟨3174467944288241177301685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232623925717654903068913 3174467944288241177301685)
                  ·
                    refine ⟨297606369777022610372033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3174467944288241177301685 297606369777022610372033)
                    ·
                      rfl

theorem cell23_1738759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1738759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738759 prefixEnd_1738759 := by exact prefixLift 1738759
  have htrace : WordTrace (prefixWord ++ tailWord_1738759) baseStart_1738759 baseEnd_1738759 := by
    simpa [prefixWord, tailWord_1738759, baseEnd_1738759] using wordTrace_append hprefix tailTrace_1738759
  have hstable : (prefixWord ++ tailWord_1738759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738759).length < 2 ^ (prefixWord ++ tailWord_1738759).sum := by decide
  have hdescent : baseEnd_1738759 < baseStart_1738759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738789 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_1738789 : Nat := 118140960795 + 1738789 * 2 ^ 59
def prefixEnd_1738789 : Nat := 4983230072969 + 3 ^ 40 * 1738789 * 2
def baseEnd_1738789 : Nat := 297611504583567571246987

theorem tailTrace_1738789 : CollatzResearch.WordTrace tailWord_1738789 prefixEnd_1738789 297611504583567571246987 := by
  unfold tailWord_1738789
  simp only [CollatzResearch.WordTrace]
  refine ⟨63418844897671889363995421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42279229931781259575996947 63418844897671889363995421)
  ·
    refine ⟨23782066836626958511498283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63418844897671889363995421 23782066836626958511498283)
    ·
      refine ⟨35673100254940437767247425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23782066836626958511498283 35673100254940437767247425)
      ·
        refine ⟨26754825191205328325435569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35673100254940437767247425 26754825191205328325435569)
        ·
          refine ⟨20066118893403996244076677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26754825191205328325435569 20066118893403996244076677)
          ·
            refine ⟨3762397292513249295764377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20066118893403996244076677 3762397292513249295764377)
            ·
              refine ⟨2821797969384936971823283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762397292513249295764377 2821797969384936971823283)
              ·
                refine ⟨4232696954077405457734925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821797969384936971823283 4232696954077405457734925)
                ·
                  refine ⟨1587261357779027046650597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4232696954077405457734925 1587261357779027046650597)
                  ·
                    refine ⟨297611504583567571246987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587261357779027046650597 297611504583567571246987)
                    ·
                      rfl

theorem cell23_1738789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_1738789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738789 prefixEnd_1738789 := by exact prefixLift 1738789
  have htrace : WordTrace (prefixWord ++ tailWord_1738789) baseStart_1738789 baseEnd_1738789 := by
    simpa [prefixWord, tailWord_1738789, baseEnd_1738789] using wordTrace_append hprefix tailTrace_1738789
  have hstable : (prefixWord ++ tailWord_1738789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738789).length < 2 ^ (prefixWord ++ tailWord_1738789).sum := by decide
  have hdescent : baseEnd_1738789 < baseStart_1738789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738812 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1738812 : Nat := 118140960795 + 1738812 * 2 ^ 59
def prefixEnd_1738812 : Nat := 4983230072969 + 3 ^ 40 * 1738812 * 2
def baseEnd_1738812 : Nat := 892846323805756123753355

theorem tailTrace_1738812 : CollatzResearch.WordTrace tailWord_1738812 prefixEnd_1738812 892846323805756123753355 := by
  unfold tailWord_1738812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709841888294282146041345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42279789184392376194721793 31709841888294282146041345)
  ·
    refine ⟨23782381416220711609531009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31709841888294282146041345 23782381416220711609531009)
    ·
      refine ⟨17836786062165533707148257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23782381416220711609531009 17836786062165533707148257)
      ·
        refine ⟨13377589546624150280361193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17836786062165533707148257 13377589546624150280361193)
        ·
          refine ⟨10033192159968112710270895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13377589546624150280361193 10033192159968112710270895)
          ·
            refine ⟨15049788239952169065406343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033192159968112710270895 15049788239952169065406343)
            ·
              refine ⟨22574682359928253598109515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049788239952169065406343 22574682359928253598109515)
              ·
                refine ⟨33862023539892380397164273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22574682359928253598109515 33862023539892380397164273)
                ·
                  refine ⟨25396517654919285297873205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33862023539892380397164273 25396517654919285297873205)
                  ·
                    refine ⟨2380923530148682996675613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25396517654919285297873205 2380923530148682996675613)
                    ·
                      refine ⟨892846323805756123753355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2380923530148682996675613 892846323805756123753355)
                      ·
                        rfl

theorem cell23_1738812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1738812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738812 prefixEnd_1738812 := by exact prefixLift 1738812
  have htrace : WordTrace (prefixWord ++ tailWord_1738812) baseStart_1738812 baseEnd_1738812 := by
    simpa [prefixWord, tailWord_1738812, baseEnd_1738812] using wordTrace_append hprefix tailTrace_1738812
  have hstable : (prefixWord ++ tailWord_1738812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738812).length < 2 ^ (prefixWord ++ tailWord_1738812).sum := by decide
  have hdescent : baseEnd_1738812 < baseStart_1738812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738839 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_1738839 : Nat := 118140960795 + 1738839 * 2 ^ 59
def prefixEnd_1738839 : Nat := 4983230072969 + 3 ^ 40 * 1738839 * 2
def baseEnd_1738839 : Nat := 892860187783427518115731

theorem tailTrace_1738839 : CollatzResearch.WordTrace tailWord_1738839 prefixEnd_1738839 892860187783427518115731 := by
  unfold tailWord_1738839
  simp only [CollatzResearch.WordTrace]
  refine ⟨63420668547490747903315571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42280445698327165268877047 63420668547490747903315571)
  ·
    refine ⟨95131002821236121854973357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63420668547490747903315571 95131002821236121854973357)
    ·
      refine ⟨35674126057963545695615009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95131002821236121854973357 35674126057963545695615009)
      ·
        refine ⟨26755594543472659271711257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35674126057963545695615009 26755594543472659271711257)
        ·
          refine ⟨20066695907604494453783443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26755594543472659271711257 20066695907604494453783443)
          ·
            refine ⟨30100043861406741680675165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20066695907604494453783443 30100043861406741680675165)
            ·
              refine ⟨11287516448027528130253187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30100043861406741680675165 11287516448027528130253187)
              ·
                refine ⟨16931274672041292195379781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287516448027528130253187 16931274672041292195379781)
                ·
                  refine ⟨3174614001007742286633709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16931274672041292195379781 3174614001007742286633709)
                  ·
                    refine ⟨1190480250377903357487641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174614001007742286633709 1190480250377903357487641)
                    ·
                      refine ⟨892860187783427518115731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190480250377903357487641 892860187783427518115731)
                      ·
                        rfl

theorem cell23_1738839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_1738839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738839 prefixEnd_1738839 := by exact prefixLift 1738839
  have htrace : WordTrace (prefixWord ++ tailWord_1738839) baseStart_1738839 baseEnd_1738839 := by
    simpa [prefixWord, tailWord_1738839, baseEnd_1738839] using wordTrace_append hprefix tailTrace_1738839
  have hstable : (prefixWord ++ tailWord_1738839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738839).length < 2 ^ (prefixWord ++ tailWord_1738839).sum := by decide
  have hdescent : baseEnd_1738839 < baseStart_1738839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738866 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_1738866 : Nat := 118140960795 + 1738866 * 2 ^ 59
def prefixEnd_1738866 : Nat := 4983230072969 + 3 ^ 40 * 1738866 * 2
def baseEnd_1738866 : Nat := 297624683920366304159369

theorem tailTrace_1738866 : CollatzResearch.WordTrace tailWord_1738866 prefixEnd_1738866 297624683920366304159369 := by
  unfold tailWord_1738866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855413329598232878637113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42281102212261954343032301 15855413329598232878637113)
  ·
    refine ⟨11891559997198674658977835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15855413329598232878637113 11891559997198674658977835)
    ·
      refine ⟨17837339995798011988466753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11891559997198674658977835 17837339995798011988466753)
      ·
        refine ⟨13378004996848508991350065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17837339995798011988466753 13378004996848508991350065)
        ·
          refine ⟨10033503747636381743512549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13378004996848508991350065 10033503747636381743512549)
          ·
            refine ⟨1881281952681821576908603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10033503747636381743512549 1881281952681821576908603)
            ·
              refine ⟨2821922929022732365362905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881281952681821576908603 2821922929022732365362905)
              ·
                refine ⟨2116442196767049274022179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821922929022732365362905 2116442196767049274022179)
                ·
                  refine ⟨3174663295150573911033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116442196767049274022179 3174663295150573911033269)
                  ·
                    refine ⟨297624683920366304159369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3174663295150573911033269 297624683920366304159369)
                    ·
                      rfl

theorem cell23_1738866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_1738866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738866 prefixEnd_1738866 := by exact prefixLift 1738866
  have htrace : WordTrace (prefixWord ++ tailWord_1738866) baseStart_1738866 baseEnd_1738866 := by
    simpa [prefixWord, tailWord_1738866, baseEnd_1738866] using wordTrace_append hprefix tailTrace_1738866
  have hstable : (prefixWord ++ tailWord_1738866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738866).length < 2 ^ (prefixWord ++ tailWord_1738866).sum := by decide
  have hdescent : baseEnd_1738866 < baseStart_1738866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738909 : List Nat := [1, 4, 2, 1, 1, 5, 1, 8]
def baseStart_1738909 : Nat := 118140960795 + 1738909 * 2 ^ 59
def prefixEnd_1738909 : Nat := 4983230072969 + 3 ^ 40 * 1738909 * 2
def baseEnd_1738909 : Nat := 33070227089971934971867

theorem tailTrace_1738909 : CollatzResearch.WordTrace tailWord_1738909 prefixEnd_1738909 33070227089971934971867 := by
  unfold tailWord_1738909
  simp only [CollatzResearch.WordTrace]
  refine ⟨63423221657237149858363781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42282147771491433238909187 63423221657237149858363781)
  ·
    refine ⟨11891854060731965598443209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63423221657237149858363781 11891854060731965598443209)
    ·
      refine ⟨8918890545548974198832407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11891854060731965598443209 8918890545548974198832407)
      ·
        refine ⟨13378335818323461298248611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8918890545548974198832407 13378335818323461298248611)
        ·
          refine ⟨20067503727485191947372917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13378335818323461298248611 20067503727485191947372917)
          ·
            refine ⟨1881328474451736745066211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20067503727485191947372917 1881328474451736745066211)
            ·
              refine ⟨2821992711677605117599317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881328474451736745066211 2821992711677605117599317)
              ·
                refine ⟨33070227089971934971867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2821992711677605117599317 33070227089971934971867)
                ·
                  rfl

theorem cell23_1738909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 8].length) (baseStart_1738909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738909 prefixEnd_1738909 := by exact prefixLift 1738909
  have htrace : WordTrace (prefixWord ++ tailWord_1738909) baseStart_1738909 baseEnd_1738909 := by
    simpa [prefixWord, tailWord_1738909, baseEnd_1738909] using wordTrace_append hprefix tailTrace_1738909
  have hstable : (prefixWord ++ tailWord_1738909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738909).length < 2 ^ (prefixWord ++ tailWord_1738909).sum := by decide
  have hdescent : baseEnd_1738909 < baseStart_1738909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738916 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1738916 : Nat := 118140960795 + 1738916 * 2 ^ 59
def prefixEnd_1738916 : Nat := 4983230072969 + 3 ^ 40 * 1738916 * 2
def baseEnd_1738916 : Nat := 892899725793823716852877

theorem tailTrace_1738916 : CollatzResearch.WordTrace tailWord_1738916 prefixEnd_1738916 892899725793823716852877 := by
  unfold tailWord_1738916
  simp only [CollatzResearch.WordTrace]
  refine ⟨31711738484105895026934301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42282317978807860035912401 31711738484105895026934301)
  ·
    refine ⟨11891901931539710635100363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31711738484105895026934301 11891901931539710635100363)
    ·
      refine ⟨17837852897309565952650545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11891901931539710635100363 17837852897309565952650545)
      ·
        refine ⟨13378389672982174464487909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17837852897309565952650545 13378389672982174464487909)
        ·
          refine ⟨2508448063684157712091483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13378389672982174464487909 2508448063684157712091483)
          ·
            refine ⟨3762672095526236568137225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508448063684157712091483 3762672095526236568137225)
            ·
              refine ⟨2822004071644677426102919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762672095526236568137225 2822004071644677426102919)
              ·
                refine ⟨4233006107467016139154379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822004071644677426102919 4233006107467016139154379)
                ·
                  refine ⟨6349509161200524208731569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233006107467016139154379 6349509161200524208731569)
                  ·
                    refine ⟨4762131870900393156548677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349509161200524208731569 4762131870900393156548677)
                    ·
                      refine ⟨892899725793823716852877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4762131870900393156548677 892899725793823716852877)
                      ·
                        rfl

theorem cell23_1738916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1738916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738916 prefixEnd_1738916 := by exact prefixLift 1738916
  have htrace : WordTrace (prefixWord ++ tailWord_1738916) baseStart_1738916 baseEnd_1738916 := by
    simpa [prefixWord, tailWord_1738916, baseEnd_1738916] using wordTrace_append hprefix tailTrace_1738916
  have hstable : (prefixWord ++ tailWord_1738916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738916).length < 2 ^ (prefixWord ++ tailWord_1738916).sum := by decide
  have hdescent : baseEnd_1738916 < baseStart_1738916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738940 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1738940 : Nat := 118140960795 + 1738940 * 2 ^ 59
def prefixEnd_1738940 : Nat := 4983230072969 + 3 ^ 40 * 1738940 * 2
def baseEnd_1738940 : Nat := 892912049329531622952767

theorem tailTrace_1738940 : CollatzResearch.WordTrace tailWord_1738940 prefixEnd_1738940 892912049329531622952767 := by
  unfold tailWord_1738940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31712176160062421076371137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42282901546749894768494849 31712176160062421076371137)
  ·
    refine ⟨23784132120046815807278353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31712176160062421076371137 23784132120046815807278353)
    ·
      refine ⟨17838099090035111855458765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23784132120046815807278353 17838099090035111855458765)
      ·
        refine ⟨6689287158763166945797037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17838099090035111855458765 6689287158763166945797037)
        ·
          refine ⟨2508482684536187604673889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6689287158763166945797037 2508482684536187604673889)
          ·
            refine ⟨1881362013402140703505417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508482684536187604673889 1881362013402140703505417)
            ·
              refine ⟨1411021510051605527629063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881362013402140703505417 1411021510051605527629063)
              ·
                refine ⟨2116532265077408291443595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411021510051605527629063 2116532265077408291443595)
                ·
                  refine ⟨3174798397616112437165393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116532265077408291443595 3174798397616112437165393)
                  ·
                    refine ⟨2381098798212084327874045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174798397616112437165393 2381098798212084327874045)
                    ·
                      refine ⟨892912049329531622952767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381098798212084327874045 892912049329531622952767)
                      ·
                        rfl

theorem cell23_1738940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1738940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1738940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1738940 prefixEnd_1738940 := by exact prefixLift 1738940
  have htrace : WordTrace (prefixWord ++ tailWord_1738940) baseStart_1738940 baseEnd_1738940 := by
    simpa [prefixWord, tailWord_1738940, baseEnd_1738940] using wordTrace_append hprefix tailTrace_1738940
  have hstable : (prefixWord ++ tailWord_1738940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738940).length < 2 ^ (prefixWord ++ tailWord_1738940).sum := by decide
  have hdescent : baseEnd_1738940 < baseStart_1738940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739010 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_1739010 : Nat := 118140960795 + 1739010 * 2 ^ 59
def prefixEnd_1739010 : Nat := 4983230072969 + 3 ^ 40 * 1739010 * 2
def baseEnd_1739010 : Nat := 892947992975346349077445

theorem tailTrace_1739010 : CollatzResearch.WordTrace tailWord_1739010 prefixEnd_1739010 892947992975346349077445 := by
  unfold tailWord_1739010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856726357467811026947621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42284603619914162738526989 15856726357467811026947621)
  ·
    refine ⟨2973136192025214567552679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15856726357467811026947621 2973136192025214567552679)
    ·
      refine ⟨4459704288037821851329019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973136192025214567552679 4459704288037821851329019)
      ·
        refine ⟨6689556432056732776993529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459704288037821851329019 6689556432056732776993529)
        ·
          refine ⟨5017167324042549582745147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6689556432056732776993529 5017167324042549582745147)
          ·
            refine ⟨7525750986063824374117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017167324042549582745147 7525750986063824374117721)
            ·
              refine ⟨5644313239547868280588291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525750986063824374117721 5644313239547868280588291)
              ·
                refine ⟨8466469859321802420882437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644313239547868280588291 8466469859321802420882437)
                ·
                  refine ⟨1587463098622837953915457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8466469859321802420882437 1587463098622837953915457)
                  ·
                    refine ⟨1190597323967128465436593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1587463098622837953915457 1190597323967128465436593)
                    ·
                      refine ⟨892947992975346349077445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190597323967128465436593 892947992975346349077445)
                      ·
                        rfl

theorem cell23_1739010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_1739010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739010 prefixEnd_1739010 := by exact prefixLift 1739010
  have htrace : WordTrace (prefixWord ++ tailWord_1739010) baseStart_1739010 baseEnd_1739010 := by
    simpa [prefixWord, tailWord_1739010, baseEnd_1739010] using wordTrace_append hprefix tailTrace_1739010
  have hstable : (prefixWord ++ tailWord_1739010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739010).length < 2 ^ (prefixWord ++ tailWord_1739010).sum := by decide
  have hdescent : baseEnd_1739010 < baseStart_1739010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739016 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 7]
def baseStart_1739016 : Nat := 118140960795 + 1739016 * 2 ^ 59
def prefixEnd_1739016 : Nat := 4983230072969 + 3 ^ 40 * 1739016 * 2
def baseEnd_1739016 : Nat := 99216785984363702844713

theorem tailTrace_1739016 : CollatzResearch.WordTrace tailWord_1739016 prefixEnd_1739016 99216785984363702844713 := by
  unfold tailWord_1739016
  simp only [CollatzResearch.WordTrace]
  refine ⟨31713562133924753566254451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42284749511899671421672601 31713562133924753566254451)
  ·
    refine ⟨47570343200887130349381677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31713562133924753566254451 47570343200887130349381677)
    ·
      refine ⟨17838878700332673881018129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47570343200887130349381677 17838878700332673881018129)
      ·
        refine ⟨13379159025249505410763597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17838878700332673881018129 13379159025249505410763597)
        ·
          refine ⟨5017184634468564529036349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13379159025249505410763597 5017184634468564529036349)
          ·
            refine ⟨1881444237925711698388631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5017184634468564529036349 1881444237925711698388631)
            ·
              refine ⟨2822166356888567547582947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881444237925711698388631 2822166356888567547582947)
              ·
                refine ⟨4233249535332851321374421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822166356888567547582947 4233249535332851321374421)
                ·
                  refine ⟨99216785984363702844713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4233249535332851321374421 99216785984363702844713)
                  ·
                    rfl

theorem cell23_1739016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_1739016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739016 prefixEnd_1739016 := by exact prefixLift 1739016
  have htrace : WordTrace (prefixWord ++ tailWord_1739016) baseStart_1739016 baseEnd_1739016 := by
    simpa [prefixWord, tailWord_1739016, baseEnd_1739016] using wordTrace_append hprefix tailTrace_1739016
  have hstable : (prefixWord ++ tailWord_1739016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739016).length < 2 ^ (prefixWord ++ tailWord_1739016).sum := by decide
  have hdescent : baseEnd_1739016 < baseStart_1739016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739066 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1739066 : Nat := 118140960795 + 1739066 * 2 ^ 59
def prefixEnd_1739066 : Nat := 4983230072969 + 3 ^ 40 * 1739066 * 2
def baseEnd_1739066 : Nat := 892976747891998129977187

theorem tailTrace_1739066 : CollatzResearch.WordTrace tailWord_1739066 prefixEnd_1739066 892976747891998129977187 := by
  unfold tailWord_1739066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15857236979417091417957263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42285965278445577114552701 15857236979417091417957263)
  ·
    refine ⟨23785855469125637126935895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15857236979417091417957263 23785855469125637126935895)
    ·
      refine ⟨35678783203688455690403843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23785855469125637126935895 35678783203688455690403843)
      ·
        refine ⟨53518174805532683535605765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35678783203688455690403843 53518174805532683535605765)
        ·
          refine ⟨10034657776037378162926081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53518174805532683535605765 10034657776037378162926081)
          ·
            refine ⟨7525993332028033622194561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034657776037378162926081 7525993332028033622194561)
            ·
              refine ⟨5644494999021025216645921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525993332028033622194561 5644494999021025216645921)
              ·
                refine ⟨4233371249265768912484441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644494999021025216645921 4233371249265768912484441)
                ·
                  refine ⟨3175028436949326684363331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4233371249265768912484441 3175028436949326684363331)
                  ·
                    refine ⟨4762542655423990026544997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175028436949326684363331 4762542655423990026544997)
                    ·
                      refine ⟨892976747891998129977187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4762542655423990026544997 892976747891998129977187)
                      ·
                        rfl

theorem cell23_1739066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1739066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739066 prefixEnd_1739066 := by exact prefixLift 1739066
  have htrace : WordTrace (prefixWord ++ tailWord_1739066) baseStart_1739066 baseEnd_1739066 := by
    simpa [prefixWord, tailWord_1739066, baseEnd_1739066] using wordTrace_append hprefix tailTrace_1739066
  have hstable : (prefixWord ++ tailWord_1739066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739066).length < 2 ^ (prefixWord ++ tailWord_1739066).sum := by decide
  have hdescent : baseEnd_1739066 < baseStart_1739066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739093 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1739093 : Nat := 118140960795 + 1739093 * 2 ^ 59
def prefixEnd_1739093 : Nat := 4983230072969 + 3 ^ 40 * 1739093 * 2
def baseEnd_1739093 : Nat := 297663537289889841446521

theorem tailTrace_1739093 : CollatzResearch.WordTrace tailWord_1739093 prefixEnd_1739093 297663537289889841446521 := by
  unfold tailWord_1739093
  simp only [CollatzResearch.WordTrace]
  refine ⟨63429932688570549283061933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42286621792380366188707955 63429932688570549283061933)
  ·
    refine ⟨23786224758213955981148225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63429932688570549283061933 23786224758213955981148225)
    ·
      refine ⟨17839668568660466985861169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23786224758213955981148225 17839668568660466985861169)
      ·
        refine ⟨13379751426495350239395877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17839668568660466985861169 13379751426495350239395877)
        ·
          refine ⟨2508703392467878169886727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13379751426495350239395877 2508703392467878169886727)
          ·
            refine ⟨3763055088701817254830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508703392467878169886727 3763055088701817254830091)
            ·
              refine ⟨5644582633052725882245137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763055088701817254830091 5644582633052725882245137)
              ·
                refine ⟨4233436974789544411683853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644582633052725882245137 4233436974789544411683853)
                ·
                  refine ⟨1587538865546079154381445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4233436974789544411683853 1587538865546079154381445)
                  ·
                    refine ⟨297663537289889841446521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587538865546079154381445 297663537289889841446521)
                    ·
                      rfl

theorem cell23_1739093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1739093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739093 prefixEnd_1739093 := by exact prefixLift 1739093
  have htrace : WordTrace (prefixWord ++ tailWord_1739093) baseStart_1739093 baseEnd_1739093 := by
    simpa [prefixWord, tailWord_1739093, baseEnd_1739093] using wordTrace_append hprefix tailTrace_1739093
  have hstable : (prefixWord ++ tailWord_1739093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739093).length < 2 ^ (prefixWord ++ tailWord_1739093).sum := by decide
  have hdescent : baseEnd_1739093 < baseStart_1739093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739119 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 5, 5]
def baseStart_1739119 : Nat := 118140960795 + 1739119 * 2 ^ 59
def prefixEnd_1739119 : Nat := 4983230072969 + 3 ^ 40 * 1739119 * 2
def baseEnd_1739119 : Nat := 297667987455562140871481

theorem tailTrace_1739119 : CollatzResearch.WordTrace tailWord_1739119 prefixEnd_1739119 297667987455562140871481 := by
  unfold tailWord_1739119
  simp only [CollatzResearch.WordTrace]
  refine ⟨63430880986476355723508411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42287253990984237149005607 63430880986476355723508411)
  ·
    refine ⟨95146321479714533585262617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63430880986476355723508411 95146321479714533585262617)
    ·
      refine ⟨71359741109785900188946963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95146321479714533585262617 71359741109785900188946963)
      ·
        refine ⟨107039611664678850283420445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71359741109785900188946963 107039611664678850283420445)
        ·
          refine ⟨40139854374254568856282667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107039611664678850283420445 40139854374254568856282667)
          ·
            refine ⟨60209781561381853284424001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40139854374254568856282667 60209781561381853284424001)
            ·
              refine ⟨45157336171036389963318001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60209781561381853284424001 45157336171036389963318001)
              ·
                refine ⟨33868002128277292472488501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45157336171036389963318001 33868002128277292472488501)
                ·
                  refine ⟨3175125199525996169295797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33868002128277292472488501 3175125199525996169295797)
                  ·
                    refine ⟨297667987455562140871481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3175125199525996169295797 297667987455562140871481)
                    ·
                      rfl

theorem cell23_1739119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_1739119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739119 prefixEnd_1739119 := by exact prefixLift 1739119
  have htrace : WordTrace (prefixWord ++ tailWord_1739119) baseStart_1739119 baseEnd_1739119 := by
    simpa [prefixWord, tailWord_1739119, baseEnd_1739119] using wordTrace_append hprefix tailTrace_1739119
  have hstable : (prefixWord ++ tailWord_1739119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739119).length < 2 ^ (prefixWord ++ tailWord_1739119).sum := by decide
  have hdescent : baseEnd_1739119 < baseStart_1739119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739133 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1739133 : Nat := 118140960795 + 1739133 * 2 ^ 59
def prefixEnd_1739133 : Nat := 4983230072969 + 3 ^ 40 * 1739133 * 2
def baseEnd_1739133 : Nat := 893011151095849367839379

theorem tailTrace_1739133 : CollatzResearch.WordTrace tailWord_1739133 prefixEnd_1739133 893011151095849367839379 := by
  unfold tailWord_1739133
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431391608425636114518053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42287594405617090743012035 63431391608425636114518053)
  ·
    refine ⟨11893385926579806771472135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63431391608425636114518053 11893385926579806771472135)
    ·
      refine ⟨17840078889869710157208203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893385926579806771472135 17840078889869710157208203)
      ·
        refine ⟨26760118334804565235812305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17840078889869710157208203 26760118334804565235812305)
        ·
          refine ⟨20070088751103423926859229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26760118334804565235812305 20070088751103423926859229)
          ·
            refine ⟨7526283281663783972572211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20070088751103423926859229 7526283281663783972572211)
            ·
              refine ⟨11289424922495675958858317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526283281663783972572211 11289424922495675958858317)
              ·
                refine ⟨4233534345935878484571869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11289424922495675958858317 4233534345935878484571869)
                ·
                  refine ⟨1587575379725954431714451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4233534345935878484571869 1587575379725954431714451)
                  ·
                    refine ⟨2381363069588931647571677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1587575379725954431714451 2381363069588931647571677)
                    ·
                      refine ⟨893011151095849367839379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381363069588931647571677 893011151095849367839379)
                      ·
                        rfl

theorem cell23_1739133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1739133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739133 prefixEnd_1739133 := by exact prefixLift 1739133
  have htrace : WordTrace (prefixWord ++ tailWord_1739133) baseStart_1739133 baseEnd_1739133 := by
    simpa [prefixWord, tailWord_1739133, baseEnd_1739133] using wordTrace_append hprefix tailTrace_1739133
  have hstable : (prefixWord ++ tailWord_1739133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739133).length < 2 ^ (prefixWord ++ tailWord_1739133).sum := by decide
  have hdescent : baseEnd_1739133 < baseStart_1739133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
