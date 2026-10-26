import V185TrunkScan22Chunk214

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1917246 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1917246 : Nat := 118140960795 + 1917246 * 2 ^ 59
def prefixEnd_1917246 : Nat := 4983230072969 + 3 ^ 40 * 1917246 * 2
def baseEnd_1917246 : Nat := 656312487273407333271835

theorem tailTrace_1917246 : CollatzResearch.WordTrace tailWord_1917246 prefixEnd_1917246 656312487273407333271835 := by
  unfold tailWord_1917246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740963301519082049139449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46618470941435104262077061 8740963301519082049139449)
  ·
    refine ⟨6555722476139311536854587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8740963301519082049139449 6555722476139311536854587)
    ·
      refine ⟨9833583714208967305281881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6555722476139311536854587 9833583714208967305281881)
      ·
        refine ⟨7375187785656725478961411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9833583714208967305281881 7375187785656725478961411)
        ·
          refine ⟨11062781678485088218442117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375187785656725478961411 11062781678485088218442117)
          ·
            refine ⟨2074271564715954040957897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11062781678485088218442117 2074271564715954040957897)
            ·
              refine ⟨1555703673536965530718423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074271564715954040957897 1555703673536965530718423)
              ·
                refine ⟨2333555510305448296077635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555703673536965530718423 2333555510305448296077635)
                ·
                  refine ⟨3500333265458172444116453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333555510305448296077635 3500333265458172444116453)
                  ·
                    refine ⟨656312487273407333271835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500333265458172444116453 656312487273407333271835)
                    ·
                      rfl

theorem cell22_1917246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1917246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917246 prefixEnd_1917246 := by exact prefixLift 1917246
  have htrace : WordTrace (prefixWord ++ tailWord_1917246) baseStart_1917246 baseEnd_1917246 := by
    simpa [prefixWord, tailWord_1917246, baseEnd_1917246] using wordTrace_append hprefix tailTrace_1917246
  have hstable : (prefixWord ++ tailWord_1917246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917246).length < 2 ^ (prefixWord ++ tailWord_1917246).sum := by decide
  have hdescent : baseEnd_1917246 < baseStart_1917246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917276 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1917276 : Nat := 118140960795 + 1917276 * 2 ^ 59
def prefixEnd_1917276 : Nat := 4983230072969 + 3 ^ 40 * 1917276 * 2
def baseEnd_1917276 : Nat := 656322756886497255021743

theorem tailTrace_1917276 : CollatzResearch.WordTrace tailWord_1917276 prefixEnd_1917276 656322756886497255021743 := by
  unfold tailWord_1917276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964400301021985758353841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46619200401362647677805121 34964400301021985758353841)
  ·
    refine ⟨26223300225766489318765381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34964400301021985758353841 26223300225766489318765381)
    ·
      refine ⟨4916868792331216747268509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26223300225766489318765381 4916868792331216747268509)
      ·
        refine ⟨1843825797124206280225691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916868792331216747268509 1843825797124206280225691)
        ·
          refine ⟨2765738695686309420338537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843825797124206280225691 2765738695686309420338537)
          ·
            refine ⟨2074304021764732065253903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2765738695686309420338537 2074304021764732065253903)
            ·
              refine ⟨3111456032647098097880855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074304021764732065253903 3111456032647098097880855)
              ·
                refine ⟨4667184048970647146821283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111456032647098097880855 4667184048970647146821283)
                ·
                  refine ⟨7000776073455970720231925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667184048970647146821283 7000776073455970720231925)
                  ·
                    refine ⟨656322756886497255021743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000776073455970720231925 656322756886497255021743)
                    ·
                      rfl

theorem cell22_1917276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1917276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917276 prefixEnd_1917276 := by exact prefixLift 1917276
  have htrace : WordTrace (prefixWord ++ tailWord_1917276) baseStart_1917276 baseEnd_1917276 := by
    simpa [prefixWord, tailWord_1917276, baseEnd_1917276] using wordTrace_append hprefix tailTrace_1917276
  have hstable : (prefixWord ++ tailWord_1917276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917276).length < 2 ^ (prefixWord ++ tailWord_1917276).sum := by decide
  have hdescent : baseEnd_1917276 < baseStart_1917276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917347 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_1917347 : Nat := 118140960795 + 1917347 * 2 ^ 59
def prefixEnd_1917347 : Nat := 4983230072969 + 3 ^ 40 * 1917347 * 2
def baseEnd_1917347 : Nat := 656347061637476736496525

theorem tailTrace_1917347 : CollatzResearch.WordTrace tailWord_1917347 prefixEnd_1917347 656347061637476736496525 := by
  unfold tailWord_1917347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69931390184786750642542295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46620926789857833761694863 69931390184786750642542295)
  ·
    refine ⟨104897085277180125963813443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69931390184786750642542295 104897085277180125963813443)
    ·
      refine ⟨157345627915770188945720165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104897085277180125963813443 157345627915770188945720165)
      ·
        refine ⟨29502305234206910427322531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157345627915770188945720165 29502305234206910427322531)
        ·
          refine ⟨44253457851310365640983797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29502305234206910427322531 44253457851310365640983797)
          ·
            refine ⟨4148761673560346778842231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44253457851310365640983797 4148761673560346778842231)
            ·
              refine ⟨6223142510340520168263347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148761673560346778842231 6223142510340520168263347)
              ·
                refine ⟨9334713765510780252395021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223142510340520168263347 9334713765510780252395021)
                ·
                  refine ⟨3500517662066542594648133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9334713765510780252395021 3500517662066542594648133)
                  ·
                    refine ⟨656347061637476736496525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500517662066542594648133 656347061637476736496525)
                    ·
                      rfl

theorem cell22_1917347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_1917347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917347 prefixEnd_1917347 := by exact prefixLift 1917347
  have htrace : WordTrace (prefixWord ++ tailWord_1917347) baseStart_1917347 baseEnd_1917347 := by
    simpa [prefixWord, tailWord_1917347, baseEnd_1917347] using wordTrace_append hprefix tailTrace_1917347
  have hstable : (prefixWord ++ tailWord_1917347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917347).length < 2 ^ (prefixWord ++ tailWord_1917347).sum := by decide
  have hdescent : baseEnd_1917347 < baseStart_1917347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917375 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1917375 : Nat := 118140960795 + 1917375 * 2 ^ 59
def prefixEnd_1917375 : Nat := 4983230072969 + 3 ^ 40 * 1917375 * 2
def baseEnd_1917375 : Nat := 656356646609693996796439

theorem tailTrace_1917375 : CollatzResearch.WordTrace tailWord_1917375 prefixEnd_1917375 656356646609693996796439 := by
  unfold tailWord_1917375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69932411428685311424561579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46621607619123540949707719 69932411428685311424561579)
  ·
    refine ⟨104898617143027967136842369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69932411428685311424561579 104898617143027967136842369)
    ·
      refine ⟨78673962857270975352631777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104898617143027967136842369 78673962857270975352631777)
      ·
        refine ⟨59005472142953231514473833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78673962857270975352631777 59005472142953231514473833)
        ·
          refine ⟨44254104107214923635855375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59005472142953231514473833 44254104107214923635855375)
          ·
            refine ⟨66381156160822385453783063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44254104107214923635855375 66381156160822385453783063)
            ·
              refine ⟨99571734241233578180674595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66381156160822385453783063 99571734241233578180674595)
              ·
                refine ⟨149357601361850367271011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99571734241233578180674595 149357601361850367271011893)
                ·
                  refine ⟨14002275127673471931657365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149357601361850367271011893 14002275127673471931657365)
                  ·
                    refine ⟨656356646609693996796439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14002275127673471931657365 656356646609693996796439)
                    ·
                      rfl

theorem cell22_1917375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1917375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917375 prefixEnd_1917375 := by exact prefixLift 1917375
  have htrace : WordTrace (prefixWord ++ tailWord_1917375) baseStart_1917375 baseEnd_1917375 := by
    simpa [prefixWord, tailWord_1917375, baseEnd_1917375] using wordTrace_append hprefix tailTrace_1917375
  have hstable : (prefixWord ++ tailWord_1917375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917375).length < 2 ^ (prefixWord ++ tailWord_1917375).sum := by decide
  have hdescent : baseEnd_1917375 < baseStart_1917375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917439 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 3, 3]
def baseStart_1917439 : Nat := 118140960795 + 1917439 * 2 ^ 59
def prefixEnd_1917439 : Nat := 4983230072969 + 3 ^ 40 * 1917439 * 2
def baseEnd_1917439 : Nat := 656378555117619163196243

theorem tailTrace_1917439 : CollatzResearch.WordTrace tailWord_1917439 prefixEnd_1917439 656378555117619163196243 := by
  unfold tailWord_1917439
  simp only [CollatzResearch.WordTrace]
  refine ⟨69934745700453450354891371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46623163800302300236594247 69934745700453450354891371)
  ·
    refine ⟨104902118550680175532337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69934745700453450354891371 104902118550680175532337057)
    ·
      refine ⟨78676588913010131649252793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104902118550680175532337057 78676588913010131649252793)
      ·
        refine ⟨59007441684757598736939595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78676588913010131649252793 59007441684757598736939595)
        ·
          refine ⟨88511162527136398105409393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59007441684757598736939595 88511162527136398105409393)
          ·
            refine ⟨66383371895352298579057045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88511162527136398105409393 66383371895352298579057045)
            ·
              refine ⟨3111720557594638995893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66383371895352298579057045 3111720557594638995893299)
              ·
                refine ⟨4667580836391958493839949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111720557594638995893299 4667580836391958493839949)
                ·
                  refine ⟨1750342813646984435189981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4667580836391958493839949 1750342813646984435189981)
                  ·
                    refine ⟨656378555117619163196243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750342813646984435189981 656378555117619163196243)
                    ·
                      rfl

theorem cell22_1917439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_1917439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917439 prefixEnd_1917439 := by exact prefixLift 1917439
  have htrace : WordTrace (prefixWord ++ tailWord_1917439) baseStart_1917439 baseEnd_1917439 := by
    simpa [prefixWord, tailWord_1917439, baseEnd_1917439] using wordTrace_append hprefix tailTrace_1917439
  have hstable : (prefixWord ++ tailWord_1917439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917439).length < 2 ^ (prefixWord ++ tailWord_1917439).sum := by decide
  have hdescent : baseEnd_1917439 < baseStart_1917439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917512 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1917512 : Nat := 118140960795 + 1917512 * 2 ^ 59
def prefixEnd_1917512 : Nat := 4983230072969 + 3 ^ 40 * 1917512 * 2
def baseEnd_1917512 : Nat := 656403544509471306121019

theorem tailTrace_1917512 : CollatzResearch.WordTrace tailWord_1917512 prefixEnd_1917512 656403544509471306121019 := by
  unfold tailWord_1917512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968704114594491911149395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46624938819459322548199193 34968704114594491911149395)
  ·
    refine ⟨52453056171891737866724093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34968704114594491911149395 52453056171891737866724093)
    ·
      refine ⟨19669896064459401700021535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52453056171891737866724093 19669896064459401700021535)
      ·
        refine ⟨29504844096689102550032303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19669896064459401700021535 29504844096689102550032303)
        ·
          refine ⟨44257266145033653825048455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29504844096689102550032303 44257266145033653825048455)
          ·
            refine ⟨66385899217550480737572683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44257266145033653825048455 66385899217550480737572683)
            ·
              refine ⟨99578848826325721106359025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66385899217550480737572683 99578848826325721106359025)
              ·
                refine ⟨74684136619744290829769269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99578848826325721106359025 74684136619744290829769269)
                ·
                  refine ⟨7001637808101027265290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74684136619744290829769269 7001637808101027265290869)
                  ·
                    refine ⟨656403544509471306121019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7001637808101027265290869 656403544509471306121019)
                    ·
                      rfl

theorem cell22_1917512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1917512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917512 prefixEnd_1917512 := by exact prefixLift 1917512
  have htrace : WordTrace (prefixWord ++ tailWord_1917512) baseStart_1917512 baseEnd_1917512 := by
    simpa [prefixWord, tailWord_1917512, baseEnd_1917512] using wordTrace_append hprefix tailTrace_1917512
  have hstable : (prefixWord ++ tailWord_1917512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917512).length < 2 ^ (prefixWord ++ tailWord_1917512).sum := by decide
  have hdescent : baseEnd_1917512 < baseStart_1917512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917578 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1917578 : Nat := 118140960795 + 1917578 * 2 ^ 59
def prefixEnd_1917578 : Nat := 4983230072969 + 3 ^ 40 * 1917578 * 2
def baseEnd_1917578 : Nat := 656426137658269133970817

theorem tailTrace_1917578 : CollatzResearch.WordTrace tailWord_1917578 prefixEnd_1917578 656426137658269133970817 := by
  unfold tailWord_1917578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484953861737469273550347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46626543631299918062800925 17484953861737469273550347)
  ·
    refine ⟨26227430792606203910325521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17484953861737469273550347 26227430792606203910325521)
    ·
      refine ⟨19670573094454652932744141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26227430792606203910325521 19670573094454652932744141)
      ·
        refine ⟨7376464910420494849779053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19670573094454652932744141 7376464910420494849779053)
        ·
          refine ⟨2766174341407685568667145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7376464910420494849779053 2766174341407685568667145)
          ·
            refine ⟨2074630756055764176500359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766174341407685568667145 2074630756055764176500359)
            ·
              refine ⟨3111946134083646264750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074630756055764176500359 3111946134083646264750539)
              ·
                refine ⟨4667919201125469397125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111946134083646264750539 4667919201125469397125809)
                ·
                  refine ⟨3500939400844102047844357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667919201125469397125809 3500939400844102047844357)
                  ·
                    refine ⟨656426137658269133970817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500939400844102047844357 656426137658269133970817)
                    ·
                      rfl

theorem cell22_1917578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1917578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917578 prefixEnd_1917578 := by exact prefixLift 1917578
  have htrace : WordTrace (prefixWord ++ tailWord_1917578) baseStart_1917578 baseEnd_1917578 := by
    simpa [prefixWord, tailWord_1917578, baseEnd_1917578] using wordTrace_append hprefix tailTrace_1917578
  have hstable : (prefixWord ++ tailWord_1917578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917578).length < 2 ^ (prefixWord ++ tailWord_1917578).sum := by decide
  have hdescent : baseEnd_1917578 < baseStart_1917578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917587 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 9]
def baseStart_1917587 : Nat := 118140960795 + 1917587 * 2 ^ 59
def prefixEnd_1917587 : Nat := 4983230072969 + 3 ^ 40 * 1917587 * 2
def baseEnd_1917587 : Nat := 218809739514065370165263

theorem tailTrace_1917587 : CollatzResearch.WordTrace tailWord_1917587 prefixEnd_1917587 218809739514065370165263 := by
  unfold tailWord_1917587
  simp only [CollatzResearch.WordTrace]
  refine ⟨69940143703917271631279015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46626762469278181087519343 69940143703917271631279015)
  ·
    refine ⟨104910215555875907446918523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69940143703917271631279015 104910215555875907446918523)
    ·
      refine ⟨157365323333813861170377785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104910215555875907446918523 157365323333813861170377785)
      ·
        refine ⟨118023992500360395877783339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157365323333813861170377785 118023992500360395877783339)
        ·
          refine ⟨177035988750540593816675009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118023992500360395877783339 177035988750540593816675009)
          ·
            refine ⟨132776991562905445362506257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177035988750540593816675009 132776991562905445362506257)
            ·
              refine ⟨99582743672179084021879693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132776991562905445362506257 99582743672179084021879693)
              ·
                refine ⟨37343528877067156508204885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99582743672179084021879693 37343528877067156508204885)
                ·
                  refine ⟨218809739514065370165263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37343528877067156508204885 218809739514065370165263)
                  ·
                    rfl

theorem cell22_1917587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_1917587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917587 prefixEnd_1917587 := by exact prefixLift 1917587
  have htrace : WordTrace (prefixWord ++ tailWord_1917587) baseStart_1917587 baseEnd_1917587 := by
    simpa [prefixWord, tailWord_1917587, baseEnd_1917587] using wordTrace_append hprefix tailTrace_1917587
  have hstable : (prefixWord ++ tailWord_1917587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917587).length < 2 ^ (prefixWord ++ tailWord_1917587).sum := by decide
  have hdescent : baseEnd_1917587 < baseStart_1917587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917604 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1917604 : Nat := 118140960795 + 1917604 * 2 ^ 59
def prefixEnd_1917604 : Nat := 4983230072969 + 3 ^ 40 * 1917604 * 2
def baseEnd_1917604 : Nat := 218811679329871244273579

theorem tailTrace_1917604 : CollatzResearch.WordTrace tailWord_1917604 prefixEnd_1917604 218811679329871244273579 := by
  unfold tailWord_1917604
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970381872427841767323933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46627175829903789023098577 34970381872427841767323933)
  ·
    refine ⟨13113893202160440662746475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34970381872427841767323933 13113893202160440662746475)
    ·
      refine ⟨19670839803240660994119713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113893202160440662746475 19670839803240660994119713)
      ·
        refine ⟨14753129852430495745589785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19670839803240660994119713 14753129852430495745589785)
        ·
          refine ⟨11064847389322871809192339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14753129852430495745589785 11064847389322871809192339)
          ·
            refine ⟨16597271083984307713788509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064847389322871809192339 16597271083984307713788509)
            ·
              refine ⟨6223976656494115392670691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16597271083984307713788509 6223976656494115392670691)
              ·
                refine ⟨9335964984741173089006037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223976656494115392670691 9335964984741173089006037)
                ·
                  refine ⟨218811679329871244273579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9335964984741173089006037 218811679329871244273579)
                  ·
                    rfl

theorem cell22_1917604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1917604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917604 prefixEnd_1917604 := by exact prefixLift 1917604
  have htrace : WordTrace (prefixWord ++ tailWord_1917604) baseStart_1917604 baseEnd_1917604 := by
    simpa [prefixWord, tailWord_1917604, baseEnd_1917604] using wordTrace_append hprefix tailTrace_1917604
  have hstable : (prefixWord ++ tailWord_1917604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917604).length < 2 ^ (prefixWord ++ tailWord_1917604).sum := by decide
  have hdescent : baseEnd_1917604 < baseStart_1917604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917619 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_1917619 : Nat := 118140960795 + 1917619 * 2 ^ 59
def prefixEnd_1917619 : Nat := 4983230072969 + 3 ^ 40 * 1917619 * 2
def baseEnd_1917619 : Nat := 656440172796158693695691

theorem tailTrace_1917619 : CollatzResearch.WordTrace tailWord_1917619 prefixEnd_1917619 656440172796158693695691 := by
  unfold tailWord_1917619
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941310839801341096443911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46627540559867560730962607 69941310839801341096443911)
  ·
    refine ⟨104911966259702011644665867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69941310839801341096443911 104911966259702011644665867)
    ·
      refine ⟨157367949389553017466998801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104911966259702011644665867 157367949389553017466998801)
      ·
        refine ⟨118025962042164763100249101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157367949389553017466998801 118025962042164763100249101)
        ·
          refine ⟨44259735765811786162593413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118025962042164763100249101 44259735765811786162593413)
          ·
            refine ⟨8298700456089709905486265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44259735765811786162593413 8298700456089709905486265)
            ·
              refine ⟨6224025342067282429114699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298700456089709905486265 6224025342067282429114699)
              ·
                refine ⟨9336038013100923643672049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224025342067282429114699 9336038013100923643672049)
                ·
                  refine ⟨7002028509825692732754037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336038013100923643672049 7002028509825692732754037)
                  ·
                    refine ⟨656440172796158693695691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7002028509825692732754037 656440172796158693695691)
                    ·
                      rfl

theorem cell22_1917619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_1917619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917619 prefixEnd_1917619 := by exact prefixLift 1917619
  have htrace : WordTrace (prefixWord ++ tailWord_1917619) baseStart_1917619 baseEnd_1917619 := by
    simpa [prefixWord, tailWord_1917619, baseEnd_1917619] using wordTrace_append hprefix tailTrace_1917619
  have hstable : (prefixWord ++ tailWord_1917619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917619).length < 2 ^ (prefixWord ++ tailWord_1917619).sum := by decide
  have hdescent : baseEnd_1917619 < baseStart_1917619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917698 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1917698 : Nat := 118140960795 + 1917698 * 2 ^ 59
def prefixEnd_1917698 : Nat := 4983230072969 + 3 ^ 40 * 1917698 * 2
def baseEnd_1917698 : Nat := 656467216110628820970449

theorem tailTrace_1917698 : CollatzResearch.WordTrace tailWord_1917698 prefixEnd_1917698 656467216110628820970449 := by
  unfold tailWord_1917698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486048051628784397142437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46629461471010091725713165 17486048051628784397142437)
  ·
    refine ⟨3278634009680397074464207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17486048051628784397142437 3278634009680397074464207)
    ·
      refine ⟨4917951014520595611696311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278634009680397074464207 4917951014520595611696311)
      ·
        refine ⟨7376926521780893417544467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917951014520595611696311 7376926521780893417544467)
        ·
          refine ⟨11065389782671340126316701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376926521780893417544467 11065389782671340126316701)
          ·
            refine ⟨4149521168501752547368763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11065389782671340126316701 4149521168501752547368763)
            ·
              refine ⟨6224281752752628821053145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149521168501752547368763 6224281752752628821053145)
              ·
                refine ⟨4668211314564471615789859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224281752752628821053145 4668211314564471615789859)
                ·
                  refine ⟨7002316971846707423684789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668211314564471615789859 7002316971846707423684789)
                  ·
                    refine ⟨656467216110628820970449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7002316971846707423684789 656467216110628820970449)
                    ·
                      rfl

theorem cell22_1917698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1917698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917698 prefixEnd_1917698 := by exact prefixLift 1917698
  have htrace : WordTrace (prefixWord ++ tailWord_1917698) baseStart_1917698 baseEnd_1917698 := by
    simpa [prefixWord, tailWord_1917698, baseEnd_1917698] using wordTrace_append hprefix tailTrace_1917698
  have hstable : (prefixWord ++ tailWord_1917698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917698).length < 2 ^ (prefixWord ++ tailWord_1917698).sum := by decide
  have hdescent : baseEnd_1917698 < baseStart_1917698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917766 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1917766 : Nat := 118140960795 + 1917766 * 2 ^ 59
def prefixEnd_1917766 : Nat := 4983230072969 + 3 ^ 40 * 1917766 * 2
def baseEnd_1917766 : Nat := 656490493900299310270241

theorem tailTrace_1917766 : CollatzResearch.WordTrace tailWord_1917766 prefixEnd_1917766 656490493900299310270241 := by
  unfold tailWord_1917766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185833511570899537563911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46631114913512523468030101 2185833511570899537563911)
  ·
    refine ⟨3278750267356349306345867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185833511570899537563911 3278750267356349306345867)
    ·
      refine ⟨4918125401034523959518801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278750267356349306345867 4918125401034523959518801)
      ·
        refine ⟨3688594050775892969639101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4918125401034523959518801 3688594050775892969639101)
        ·
          refine ⟨1383222769040959863614663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3688594050775892969639101 1383222769040959863614663)
          ·
            refine ⟨2074834153561439795421995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383222769040959863614663 2074834153561439795421995)
            ·
              refine ⟨3112251230342159693132993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074834153561439795421995 3112251230342159693132993)
              ·
                refine ⟨2334188422756619769849745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112251230342159693132993 2334188422756619769849745)
                ·
                  refine ⟨1750641317067464827387309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334188422756619769849745 1750641317067464827387309)
                  ·
                    refine ⟨656490493900299310270241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750641317067464827387309 656490493900299310270241)
                    ·
                      rfl

theorem cell22_1917766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1917766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917766 prefixEnd_1917766 := by exact prefixLift 1917766
  have htrace : WordTrace (prefixWord ++ tailWord_1917766) baseStart_1917766 baseEnd_1917766 := by
    simpa [prefixWord, tailWord_1917766, baseEnd_1917766] using wordTrace_append hprefix tailTrace_1917766
  have hstable : (prefixWord ++ tailWord_1917766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917766).length < 2 ^ (prefixWord ++ tailWord_1917766).sum := by decide
  have hdescent : baseEnd_1917766 < baseStart_1917766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917788 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1917788 : Nat := 118140960795 + 1917788 * 2 ^ 59
def prefixEnd_1917788 : Nat := 4983230072969 + 3 ^ 40 * 1917788 * 2
def baseEnd_1917788 : Nat := 656498024949898586220173

theorem tailTrace_1917788 : CollatzResearch.WordTrace tailWord_1917788 prefixEnd_1917788 656498024949898586220173 := by
  unfold tailWord_1917788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34973737388094541479673009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46631649850792721972897345 34973737388094541479673009)
  ·
    refine ⟨26230303041070906109754757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34973737388094541479673009 26230303041070906109754757)
    ·
      refine ⟨4918181820200794895579017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26230303041070906109754757 4918181820200794895579017)
      ·
        refine ⟨3688636365150596171684263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4918181820200794895579017 3688636365150596171684263)
        ·
          refine ⟨5532954547725894257526395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688636365150596171684263 5532954547725894257526395)
          ·
            refine ⟨8299431821588841386289593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532954547725894257526395 8299431821588841386289593)
            ·
              refine ⟨6224573866191631039717195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299431821588841386289593 6224573866191631039717195)
              ·
                refine ⟨9336860799287446559575793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224573866191631039717195 9336860799287446559575793)
                ·
                  refine ⟨7002645599465584919681845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336860799287446559575793 7002645599465584919681845)
                  ·
                    refine ⟨656498024949898586220173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7002645599465584919681845 656498024949898586220173)
                    ·
                      rfl

theorem cell22_1917788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1917788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917788 prefixEnd_1917788 := by exact prefixLift 1917788
  have htrace : WordTrace (prefixWord ++ tailWord_1917788) baseStart_1917788 baseEnd_1917788 := by
    simpa [prefixWord, tailWord_1917788, baseEnd_1917788] using wordTrace_append hprefix tailTrace_1917788
  have hstable : (prefixWord ++ tailWord_1917788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917788).length < 2 ^ (prefixWord ++ tailWord_1917788).sum := by decide
  have hdescent : baseEnd_1917788 < baseStart_1917788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917833 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_1917833 : Nat := 118140960795 + 1917833 * 2 ^ 59
def prefixEnd_1917833 : Nat := 4983230072969 + 3 ^ 40 * 1917833 * 2
def baseEnd_1917833 : Nat := 656513429369533468845035

theorem tailTrace_1917833 : CollatzResearch.WordTrace tailWord_1917833 prefixEnd_1917833 656513429369533468845035 := by
  unfold tailWord_1917833
  simp only [CollatzResearch.WordTrace]
  refine ⟨69949116061026055644734153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46632744040684037096489435 69949116061026055644734153)
  ·
    refine ⟨52461837045769541733550615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69949116061026055644734153 52461837045769541733550615)
    ·
      refine ⟨78692755568654312600325923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52461837045769541733550615 78692755568654312600325923)
      ·
        refine ⟨118039133352981468900488885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78692755568654312600325923 118039133352981468900488885)
        ·
          refine ⟨11066168751842012709420833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118039133352981468900488885 11066168751842012709420833)
          ·
            refine ⟨8299626563881509532065625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066168751842012709420833 8299626563881509532065625)
            ·
              refine ⟨6224719922911132149049219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299626563881509532065625 6224719922911132149049219)
              ·
                refine ⟨9337079884366698223573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224719922911132149049219 9337079884366698223573829)
                ·
                  refine ⟨1750702478318755916920093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9337079884366698223573829 1750702478318755916920093)
                  ·
                    refine ⟨656513429369533468845035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750702478318755916920093 656513429369533468845035)
                    ·
                      rfl

theorem cell22_1917833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_1917833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917833 prefixEnd_1917833 := by exact prefixLift 1917833
  have htrace : WordTrace (prefixWord ++ tailWord_1917833) baseStart_1917833 baseEnd_1917833 := by
    simpa [prefixWord, tailWord_1917833, baseEnd_1917833] using wordTrace_append hprefix tailTrace_1917833
  have hstable : (prefixWord ++ tailWord_1917833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917833).length < 2 ^ (prefixWord ++ tailWord_1917833).sum := by decide
  have hdescent : baseEnd_1917833 < baseStart_1917833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917936 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_1917936 : Nat := 118140960795 + 1917936 * 2 ^ 59
def prefixEnd_1917936 : Nat := 4983230072969 + 3 ^ 40 * 1917936 * 2
def baseEnd_1917936 : Nat := 218849562791491844506573

theorem tailTrace_1917936 : CollatzResearch.WordTrace tailWord_1917936 prefixEnd_1917936 218849562791491844506573 := by
  unfold tailWord_1917936
  simp only [CollatzResearch.WordTrace]
  refine ⟨34976436389826452117866831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46635248519768602823822441 34976436389826452117866831)
  ·
    refine ⟨52464654584739678176800247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34976436389826452117866831 52464654584739678176800247)
    ·
      refine ⟨78696981877109517265200371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52464654584739678176800247 78696981877109517265200371)
      ·
        refine ⟨118045472815664275897800557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78696981877109517265200371 118045472815664275897800557)
        ·
          refine ⟨44267052305874103461675209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118045472815664275897800557 44267052305874103461675209)
          ·
            refine ⟨33200289229405577596256407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44267052305874103461675209 33200289229405577596256407)
            ·
              refine ⟨49800433844108366394384611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33200289229405577596256407 49800433844108366394384611)
              ·
                refine ⟨74700650766162549591576917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49800433844108366394384611 74700650766162549591576917)
                ·
                  refine ⟨218849562791491844506573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74700650766162549591576917 218849562791491844506573)
                  ·
                    rfl

theorem cell22_1917936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_1917936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917936 prefixEnd_1917936 := by exact prefixLift 1917936
  have htrace : WordTrace (prefixWord ++ tailWord_1917936) baseStart_1917936 baseEnd_1917936 := by
    simpa [prefixWord, tailWord_1917936, baseEnd_1917936] using wordTrace_append hprefix tailTrace_1917936
  have hstable : (prefixWord ++ tailWord_1917936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917936).length < 2 ^ (prefixWord ++ tailWord_1917936).sum := by decide
  have hdescent : baseEnd_1917936 < baseStart_1917936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917942 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1917942 : Nat := 118140960795 + 1917942 * 2 ^ 59
def prefixEnd_1917942 : Nat := 4983230072969 + 3 ^ 40 * 1917942 * 2
def baseEnd_1917942 : Nat := 218850247432364505956567

theorem tailTrace_1917942 : CollatzResearch.WordTrace tailWord_1917942 prefixEnd_1917942 218850247432364505956567 := by
  unfold tailWord_1917942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372068226101947953778255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46635394411754111506968053 4372068226101947953778255)
  ·
    refine ⟨6558102339152921930667383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4372068226101947953778255 6558102339152921930667383)
    ·
      refine ⟨9837153508729382896001075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558102339152921930667383 9837153508729382896001075)
      ·
        refine ⟨14755730263094074344001613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837153508729382896001075 14755730263094074344001613)
        ·
          refine ⟨5533398848660277879000605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14755730263094074344001613 5533398848660277879000605)
          ·
            refine ⟨2075024568247604204625227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5533398848660277879000605 2075024568247604204625227)
            ·
              refine ⟨3112536852371406306937841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075024568247604204625227 3112536852371406306937841)
              ·
                refine ⟨2334402639278554730203381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112536852371406306937841 2334402639278554730203381)
                ·
                  refine ⟨218850247432364505956567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334402639278554730203381 218850247432364505956567)
                  ·
                    rfl

theorem cell22_1917942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1917942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917942 prefixEnd_1917942 := by exact prefixLift 1917942
  have htrace : WordTrace (prefixWord ++ tailWord_1917942) baseStart_1917942 baseEnd_1917942 := by
    simpa [prefixWord, tailWord_1917942, baseEnd_1917942] using wordTrace_append hprefix tailTrace_1917942
  have hstable : (prefixWord ++ tailWord_1917942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917942).length < 2 ^ (prefixWord ++ tailWord_1917942).sum := by decide
  have hdescent : baseEnd_1917942 < baseStart_1917942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917951 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1917951 : Nat := 118140960795 + 1917951 * 2 ^ 59
def prefixEnd_1917951 : Nat := 4983230072969 + 3 ^ 40 * 1917951 * 2
def baseEnd_1917951 : Nat := 656553823181020494394673

theorem tailTrace_1917951 : CollatzResearch.WordTrace tailWord_1917951 prefixEnd_1917951 656553823181020494394673 := by
  unfold tailWord_1917951
  simp only [CollatzResearch.WordTrace]
  refine ⟨69953419874598561797529707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46635613249732374531686471 69953419874598561797529707)
  ·
    refine ⟨104930129811897842696294561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69953419874598561797529707 104930129811897842696294561)
    ·
      refine ⟨78697597358923382022220921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104930129811897842696294561 78697597358923382022220921)
      ·
        refine ⟨59023198019192536516665691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78697597358923382022220921 59023198019192536516665691)
        ·
          refine ⟨88534797028788804774998537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59023198019192536516665691 88534797028788804774998537)
          ·
            refine ⟨66401097771591603581248903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88534797028788804774998537 66401097771591603581248903)
            ·
              refine ⟨99601646657387405371873355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66401097771591603581248903 99601646657387405371873355)
              ·
                refine ⟨149402469986081108057810033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99601646657387405371873355 149402469986081108057810033)
                ·
                  refine ⟨112051852489560831043357525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149402469986081108057810033 112051852489560831043357525)
                  ·
                    refine ⟨656553823181020494394673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112051852489560831043357525 656553823181020494394673)
                    ·
                      rfl

theorem cell22_1917951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1917951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917951 prefixEnd_1917951 := by exact prefixLift 1917951
  have htrace : WordTrace (prefixWord ++ tailWord_1917951) baseStart_1917951 baseEnd_1917951 := by
    simpa [prefixWord, tailWord_1917951, baseEnd_1917951] using wordTrace_append hprefix tailTrace_1917951
  have hstable : (prefixWord ++ tailWord_1917951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917951).length < 2 ^ (prefixWord ++ tailWord_1917951).sum := by decide
  have hdescent : baseEnd_1917951 < baseStart_1917951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917953 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 6]
def baseStart_1917953 : Nat := 118140960795 + 1917953 * 2 ^ 59
def prefixEnd_1917953 : Nat := 4983230072969 + 3 ^ 40 * 1917953 * 2
def baseEnd_1917953 : Nat := 218851502607297718614889

theorem tailTrace_1917953 : CollatzResearch.WordTrace tailWord_1917953 prefixEnd_1917953 218851502607297718614889 := by
  unfold tailWord_1917953
  simp only [CollatzResearch.WordTrace]
  refine ⟨69953492820591316139102513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46635661880394210759401675 69953492820591316139102513)
  ·
    refine ⟨52465119615443487104326885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69953492820591316139102513 52465119615443487104326885)
    ·
      refine ⟨9837209927895653832061291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52465119615443487104326885 9837209927895653832061291)
      ·
        refine ⟨14755814891843480748091937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837209927895653832061291 14755814891843480748091937)
        ·
          refine ⟨11066861168882610561068953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14755814891843480748091937 11066861168882610561068953)
          ·
            refine ⟨8300145876661957920801715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066861168882610561068953 8300145876661957920801715)
            ·
              refine ⟨12450218814992936881202573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300145876661957920801715 12450218814992936881202573)
              ·
                refine ⟨4668832055622351330450965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12450218814992936881202573 4668832055622351330450965)
                ·
                  refine ⟨218851502607297718614889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4668832055622351330450965 218851502607297718614889)
                  ·
                    rfl

theorem cell22_1917953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_1917953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917953 prefixEnd_1917953 := by exact prefixLift 1917953
  have htrace : WordTrace (prefixWord ++ tailWord_1917953) baseStart_1917953 baseEnd_1917953 := by
    simpa [prefixWord, tailWord_1917953, baseEnd_1917953] using wordTrace_append hprefix tailTrace_1917953
  have hstable : (prefixWord ++ tailWord_1917953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917953).length < 2 ^ (prefixWord ++ tailWord_1917953).sum := by decide
  have hdescent : baseEnd_1917953 < baseStart_1917953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917968 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_1917968 : Nat := 118140960795 + 1917968 * 2 ^ 59
def prefixEnd_1917968 : Nat := 4983230072969 + 3 ^ 40 * 1917968 * 2
def baseEnd_1917968 : Nat := 656559642628438116719621

theorem tailTrace_1917968 : CollatzResearch.WordTrace tailWord_1917968 prefixEnd_1917968 656559642628438116719621 := by
  unfold tailWord_1917968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34977019957768486850449279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46636026610357982467265705 34977019957768486850449279)
  ·
    refine ⟨52465529936652730275673919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34977019957768486850449279 52465529936652730275673919)
    ·
      refine ⟨78698294904979095413510879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52465529936652730275673919 78698294904979095413510879)
      ·
        refine ⟨118047442357468643120266319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78698294904979095413510879 118047442357468643120266319)
        ·
          refine ⟨177071163536202964680399479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118047442357468643120266319 177071163536202964680399479)
          ·
            refine ⟨265606745304304447020599219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177071163536202964680399479 265606745304304447020599219)
            ·
              refine ⟨398410117956456670530898829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265606745304304447020599219 398410117956456670530898829)
              ·
                refine ⟨149403794233671251449087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398410117956456670530898829 149403794233671251449087061)
                ·
                  refine ⟨1750825713675834977918989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 149403794233671251449087061 1750825713675834977918989)
                  ·
                    refine ⟨656559642628438116719621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750825713675834977918989 656559642628438116719621)
                    ·
                      rfl

theorem cell22_1917968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_1917968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917968 prefixEnd_1917968 := by exact prefixLift 1917968
  have htrace : WordTrace (prefixWord ++ tailWord_1917968) baseStart_1917968 baseEnd_1917968 := by
    simpa [prefixWord, tailWord_1917968, baseEnd_1917968] using wordTrace_append hprefix tailTrace_1917968
  have hstable : (prefixWord ++ tailWord_1917968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917968).length < 2 ^ (prefixWord ++ tailWord_1917968).sum := by decide
  have hdescent : baseEnd_1917968 < baseStart_1917968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917983 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1917983 : Nat := 118140960795 + 1917983 * 2 ^ 59
def prefixEnd_1917983 : Nat := 4983230072969 + 3 ^ 40 * 1917983 * 2
def baseEnd_1917983 : Nat := 656564777434983077594575

theorem tailTrace_1917983 : CollatzResearch.WordTrace tailWord_1917983 prefixEnd_1917983 656564777434983077594575 := by
  unfold tailWord_1917983
  simp only [CollatzResearch.WordTrace]
  refine ⟨69954587010482631262694603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46636391340321754175129735 69954587010482631262694603)
  ·
    refine ⟨104931880515723946894041905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69954587010482631262694603 104931880515723946894041905)
    ·
      refine ⟨78698910386792960170531429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104931880515723946894041905 78698910386792960170531429)
      ·
        refine ⟨14756045697523680031974643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78698910386792960170531429 14756045697523680031974643)
        ·
          refine ⟨22134068546285520047961965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756045697523680031974643 22134068546285520047961965)
          ·
            refine ⟨8300275704857070017985737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22134068546285520047961965 8300275704857070017985737)
            ·
              refine ⟨6225206778642802513489303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8300275704857070017985737 6225206778642802513489303)
              ·
                refine ⟨9337810167964203770233955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225206778642802513489303 9337810167964203770233955)
                ·
                  refine ⟨14006715251946305655350933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337810167964203770233955 14006715251946305655350933)
                  ·
                    refine ⟨656564777434983077594575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14006715251946305655350933 656564777434983077594575)
                    ·
                      rfl

theorem cell22_1917983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1917983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917983 prefixEnd_1917983 := by exact prefixLift 1917983
  have htrace : WordTrace (prefixWord ++ tailWord_1917983) baseStart_1917983 baseEnd_1917983 := by
    simpa [prefixWord, tailWord_1917983, baseEnd_1917983] using wordTrace_append hprefix tailTrace_1917983
  have hstable : (prefixWord ++ tailWord_1917983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917983).length < 2 ^ (prefixWord ++ tailWord_1917983).sum := by decide
  have hdescent : baseEnd_1917983 < baseStart_1917983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917985 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1917985 : Nat := 118140960795 + 1917985 * 2 ^ 59
def prefixEnd_1917985 : Nat := 4983230072969 + 3 ^ 40 * 1917985 * 2
def baseEnd_1917985 : Nat := 656565462075855739044569

theorem tailTrace_1917985 : CollatzResearch.WordTrace tailWord_1917985 prefixEnd_1917985 656565462075855739044569 := by
  unfold tailWord_1917985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69954659956475385604267409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46636439970983590402844939 69954659956475385604267409)
  ·
    refine ⟨52465994967356539203200557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69954659956475385604267409 52465994967356539203200557)
    ·
      refine ⟨19674748112758702201200209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52465994967356539203200557 19674748112758702201200209)
      ·
        refine ⟨14756061084569026650900157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19674748112758702201200209 14756061084569026650900157)
        ·
          refine ⟨5533522906713384994087559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14756061084569026650900157 5533522906713384994087559)
          ·
            refine ⟨8300284360070077491131339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533522906713384994087559 8300284360070077491131339)
            ·
              refine ⟨12450426540105116236697009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300284360070077491131339 12450426540105116236697009)
              ·
                refine ⟨9337819905078837177522757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12450426540105116236697009 9337819905078837177522757)
                ·
                  refine ⟨1750841232202281970785517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9337819905078837177522757 1750841232202281970785517)
                  ·
                    refine ⟨656565462075855739044569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750841232202281970785517 656565462075855739044569)
                    ·
                      rfl

theorem cell22_1917985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1917985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917985 prefixEnd_1917985 := by exact prefixLift 1917985
  have htrace : WordTrace (prefixWord ++ tailWord_1917985) baseStart_1917985 baseEnd_1917985 := by
    simpa [prefixWord, tailWord_1917985, baseEnd_1917985] using wordTrace_append hprefix tailTrace_1917985
  have hstable : (prefixWord ++ tailWord_1917985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917985).length < 2 ^ (prefixWord ++ tailWord_1917985).sum := by decide
  have hdescent : baseEnd_1917985 < baseStart_1917985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917987 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 4]
def baseStart_1917987 : Nat := 118140960795 + 1917987 * 2 ^ 59
def prefixEnd_1917987 : Nat := 4983230072969 + 3 ^ 40 * 1917987 * 2
def baseEnd_1917987 : Nat := 218855382238909466831521

theorem tailTrace_1917987 : CollatzResearch.WordTrace tailWord_1917987 prefixEnd_1917987 218855382238909466831521 := by
  unfold tailWord_1917987
  simp only [CollatzResearch.WordTrace]
  refine ⟨69954732902468139945840215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46636488601645426630560143 69954732902468139945840215)
  ·
    refine ⟨104932099353702209918760323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69954732902468139945840215 104932099353702209918760323)
    ·
      refine ⟨157398149030553314878140485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104932099353702209918760323 157398149030553314878140485)
      ·
        refine ⟨29512152943228746539651341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157398149030553314878140485 29512152943228746539651341)
        ·
          refine ⟨11067057353710779952369253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29512152943228746539651341 11067057353710779952369253)
          ·
            refine ⟨2075073253820771241069235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11067057353710779952369253 2075073253820771241069235)
            ·
              refine ⟨3112609880731156861603853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075073253820771241069235 3112609880731156861603853)
              ·
                refine ⟨1167228705274183823101445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112609880731156861603853 1167228705274183823101445)
                ·
                  refine ⟨218855382238909466831521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167228705274183823101445 218855382238909466831521)
                  ·
                    rfl

theorem cell22_1917987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 4].length) (baseStart_1917987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917987 prefixEnd_1917987 := by exact prefixLift 1917987
  have htrace : WordTrace (prefixWord ++ tailWord_1917987) baseStart_1917987 baseEnd_1917987 := by
    simpa [prefixWord, tailWord_1917987, baseEnd_1917987] using wordTrace_append hprefix tailTrace_1917987
  have hstable : (prefixWord ++ tailWord_1917987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917987).length < 2 ^ (prefixWord ++ tailWord_1917987).sum := by decide
  have hdescent : baseEnd_1917987 < baseStart_1917987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918030 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_1918030 : Nat := 118140960795 + 1918030 * 2 ^ 59
def prefixEnd_1918030 : Nat := 4983230072969 + 3 ^ 40 * 1918030 * 2
def baseEnd_1918030 : Nat := 656580866495490621669431

theorem tailTrace_1918030 : CollatzResearch.WordTrace tailWord_1918030 prefixEnd_1918030 656580866495490621669431 := by
  unfold tailWord_1918030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744537655164044786206943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46637534160874905526437029 8744537655164044786206943)
  ·
    refine ⟨13116806482746067179310415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8744537655164044786206943 13116806482746067179310415)
    ·
      refine ⟨19675209724119100768965623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116806482746067179310415 19675209724119100768965623)
      ·
        refine ⟨29512814586178651153448435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19675209724119100768965623 29512814586178651153448435)
        ·
          refine ⟨44269221879267976730172653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29512814586178651153448435 44269221879267976730172653)
          ·
            refine ⟨16600958204725491273814745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44269221879267976730172653 16600958204725491273814745)
            ·
              refine ⟨12450718653544118455361059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16600958204725491273814745 12450718653544118455361059)
              ·
                refine ⟨18676077980316177683041589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450718653544118455361059 18676077980316177683041589)
                ·
                  refine ⟨1750882310654641657785149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18676077980316177683041589 1750882310654641657785149)
                  ·
                    refine ⟨656580866495490621669431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750882310654641657785149 656580866495490621669431)
                    ·
                      rfl

theorem cell22_1918030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_1918030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918030 prefixEnd_1918030 := by exact prefixLift 1918030
  have htrace : WordTrace (prefixWord ++ tailWord_1918030) baseStart_1918030 baseEnd_1918030 := by
    simpa [prefixWord, tailWord_1918030, baseEnd_1918030] using wordTrace_append hprefix tailTrace_1918030
  have hstable : (prefixWord ++ tailWord_1918030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918030).length < 2 ^ (prefixWord ++ tailWord_1918030).sum := by decide
  have hdescent : baseEnd_1918030 < baseStart_1918030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918047 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 1, 3]
def baseStart_1918047 : Nat := 118140960795 + 1918047 * 2 ^ 59
def prefixEnd_1918047 : Nat := 4983230072969 + 3 ^ 40 * 1918047 * 2
def baseEnd_1918047 : Nat := 656586685942908243994379

theorem tailTrace_1918047 : CollatzResearch.WordTrace tailWord_1918047 prefixEnd_1918047 656586685942908243994379 := by
  unfold tailWord_1918047
  simp only [CollatzResearch.WordTrace]
  refine ⟨69956921282250770193024395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46637947521500513462016263 69956921282250770193024395)
  ·
    refine ⟨104935381923376155289536593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69956921282250770193024395 104935381923376155289536593)
    ·
      refine ⟨78701536442532116467152445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104935381923376155289536593 78701536442532116467152445)
      ·
        refine ⟨29513076165949543675182167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78701536442532116467152445 29513076165949543675182167)
        ·
          refine ⟨44269614248924315512773251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29513076165949543675182167 44269614248924315512773251)
          ·
            refine ⟨66404421373386473269159877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44269614248924315512773251 66404421373386473269159877)
            ·
              refine ⟨12450829007509963737967477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66404421373386473269159877 12450829007509963737967477)
              ·
                refine ⟨1167265219454059100434451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12450829007509963737967477 1167265219454059100434451)
                ·
                  refine ⟨1750897829181088650651677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167265219454059100434451 1750897829181088650651677)
                  ·
                    refine ⟨656586685942908243994379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750897829181088650651677 656586685942908243994379)
                    ·
                      rfl

theorem cell22_1918047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_1918047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918047 prefixEnd_1918047 := by exact prefixLift 1918047
  have htrace : WordTrace (prefixWord ++ tailWord_1918047) baseStart_1918047 baseEnd_1918047 := by
    simpa [prefixWord, tailWord_1918047, baseEnd_1918047] using wordTrace_append hprefix tailTrace_1918047
  have hstable : (prefixWord ++ tailWord_1918047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918047).length < 2 ^ (prefixWord ++ tailWord_1918047).sum := by decide
  have hdescent : baseEnd_1918047 < baseStart_1918047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918060 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_1918060 : Nat := 118140960795 + 1918060 * 2 ^ 59
def prefixEnd_1918060 : Nat := 4983230072969 + 3 ^ 40 * 1918060 * 2
def baseEnd_1918060 : Nat := 218863712036193514473113

theorem tailTrace_1918060 : CollatzResearch.WordTrace tailWord_1918060 prefixEnd_1918060 218863712036193514473113 := by
  unfold tailWord_1918060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978697715601836706623817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46638263620802448942165089 34978697715601836706623817)
  ·
    refine ⟨26234023286701377529967863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34978697715601836706623817 26234023286701377529967863)
    ·
      refine ⟨39351034930052066294951795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26234023286701377529967863 39351034930052066294951795)
      ·
        refine ⟨59026552395078099442427693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39351034930052066294951795 59026552395078099442427693)
        ·
          refine ⟨22134957148154287290910385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59026552395078099442427693 22134957148154287290910385)
          ·
            refine ⟨16601217861115715468182789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22134957148154287290910385 16601217861115715468182789)
            ·
              refine ⟨3112728348959196650284273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16601217861115715468182789 3112728348959196650284273)
              ·
                refine ⟨2334546261719397487713205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112728348959196650284273 2334546261719397487713205)
                ·
                  refine ⟨218863712036193514473113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334546261719397487713205 218863712036193514473113)
                  ·
                    rfl

theorem cell22_1918060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_1918060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918060 prefixEnd_1918060 := by exact prefixLift 1918060
  have htrace : WordTrace (prefixWord ++ tailWord_1918060) baseStart_1918060 baseEnd_1918060 := by
    simpa [prefixWord, tailWord_1918060, baseEnd_1918060] using wordTrace_append hprefix tailTrace_1918060
  have hstable : (prefixWord ++ tailWord_1918060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918060).length < 2 ^ (prefixWord ++ tailWord_1918060).sum := by decide
  have hdescent : baseEnd_1918060 < baseStart_1918060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918090 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1918090 : Nat := 118140960795 + 1918090 * 2 ^ 59
def prefixEnd_1918090 : Nat := 4983230072969 + 3 ^ 40 * 1918090 * 2
def baseEnd_1918090 : Nat := 656601405721670465169247

theorem tailTrace_1918090 : CollatzResearch.WordTrace tailWord_1918090 prefixEnd_1918090 656601405721670465169247 := by
  unfold tailWord_1918090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489622405273747134209931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46638993080729992357893149 17489622405273747134209931)
  ·
    refine ⟨26234433607910620701314897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489622405273747134209931 26234433607910620701314897)
    ·
      refine ⟨19675825205932965525986173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26234433607910620701314897 19675825205932965525986173)
      ·
        refine ⟨7378434452224862072244815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19675825205932965525986173 7378434452224862072244815)
        ·
          refine ⟨11067651678337293108367223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378434452224862072244815 11067651678337293108367223)
          ·
            refine ⟨16601477517505939662550835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067651678337293108367223 16601477517505939662550835)
            ·
              refine ⟨24902216276258909493826253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16601477517505939662550835 24902216276258909493826253)
              ·
                refine ⟨9338331103597091060184845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24902216276258909493826253 9338331103597091060184845)
                ·
                  refine ⟨3501874163848909147569317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9338331103597091060184845 3501874163848909147569317)
                  ·
                    refine ⟨656601405721670465169247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3501874163848909147569317 656601405721670465169247)
                    ·
                      rfl

theorem cell22_1918090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1918090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918090 prefixEnd_1918090 := by exact prefixLift 1918090
  have htrace : WordTrace (prefixWord ++ tailWord_1918090) baseStart_1918090 baseEnd_1918090 := by
    simpa [prefixWord, tailWord_1918090, baseEnd_1918090] using wordTrace_append hprefix tailTrace_1918090
  have hstable : (prefixWord ++ tailWord_1918090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918090).length < 2 ^ (prefixWord ++ tailWord_1918090).sum := by decide
  have hdescent : baseEnd_1918090 < baseStart_1918090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918122 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1918122 : Nat := 118140960795 + 1918122 * 2 ^ 59
def prefixEnd_1918122 : Nat := 4983230072969 + 3 ^ 40 * 1918122 * 2
def baseEnd_1918122 : Nat := 218870786658544349456383

theorem tailTrace_1918122 : CollatzResearch.WordTrace tailWord_1918122 prefixEnd_1918122 218870786658544349456383 := by
  unfold tailWord_1918122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489914189244764500501155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46639771171319372001336413 17489914189244764500501155)
  ·
    refine ⟨26234871283867146750751733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17489914189244764500501155 26234871283867146750751733)
    ·
      refine ⟨2459519182862545007882975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26234871283867146750751733 2459519182862545007882975)
      ·
        refine ⟨3689278774293817511824463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459519182862545007882975 3689278774293817511824463)
        ·
          refine ⟨5533918161440726267736695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689278774293817511824463 5533918161440726267736695)
          ·
            refine ⟨8300877242161089401605043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533918161440726267736695 8300877242161089401605043)
            ·
              refine ⟨12451315863241634102407565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300877242161089401605043 12451315863241634102407565)
              ·
                refine ⟨4669243448715612788402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12451315863241634102407565 4669243448715612788402837)
                ·
                  refine ⟨218870786658544349456383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4669243448715612788402837 218870786658544349456383)
                  ·
                    rfl

theorem cell22_1918122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1918122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918122 prefixEnd_1918122 := by exact prefixLift 1918122
  have htrace : WordTrace (prefixWord ++ tailWord_1918122) baseStart_1918122 baseEnd_1918122 := by
    simpa [prefixWord, tailWord_1918122, baseEnd_1918122] using wordTrace_append hprefix tailTrace_1918122
  have hstable : (prefixWord ++ tailWord_1918122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918122).length < 2 ^ (prefixWord ++ tailWord_1918122).sum := by decide
  have hdescent : baseEnd_1918122 < baseStart_1918122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918137 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_1918137 : Nat := 118140960795 + 1918137 * 2 ^ 59
def prefixEnd_1918137 : Nat := 4983230072969 + 3 ^ 40 * 1918137 * 2
def baseEnd_1918137 : Nat := 656617494782178009244103

theorem tailTrace_1918137 : CollatzResearch.WordTrace tailWord_1918137 prefixEnd_1918137 656617494782178009244103 := by
  unfold tailWord_1918137
  simp only [CollatzResearch.WordTrace]
  refine ⟨69960203851924715563800665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46640135901283143709200443 69960203851924715563800665)
  ·
    refine ⟨52470152888943536672850499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69960203851924715563800665 52470152888943536672850499)
    ·
      refine ⟨78705229333415305009275749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52470152888943536672850499 78705229333415305009275749)
      ·
        refine ⟨14757230500015369689239203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78705229333415305009275749 14757230500015369689239203)
        ·
          refine ⟨22135845750023054533858805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757230500015369689239203 22135845750023054533858805)
          ·
            refine ⟨2075235539064661362549263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22135845750023054533858805 2075235539064661362549263)
            ·
              refine ⟨3112853308596992043823895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075235539064661362549263 3112853308596992043823895)
              ·
                refine ⟨4669279962895488065735843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112853308596992043823895 4669279962895488065735843)
                ·
                  refine ⟨7003919944343232098603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669279962895488065735843 7003919944343232098603765)
                  ·
                    refine ⟨656617494782178009244103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7003919944343232098603765 656617494782178009244103)
                    ·
                      rfl

theorem cell22_1918137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_1918137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918137 prefixEnd_1918137 := by exact prefixLift 1918137
  have htrace : WordTrace (prefixWord ++ tailWord_1918137) baseStart_1918137 baseEnd_1918137 := by
    simpa [prefixWord, tailWord_1918137, baseEnd_1918137] using wordTrace_append hprefix tailTrace_1918137
  have hstable : (prefixWord ++ tailWord_1918137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918137).length < 2 ^ (prefixWord ++ tailWord_1918137).sum := by decide
  have hdescent : baseEnd_1918137 < baseStart_1918137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918257 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 6]
def baseStart_1918257 : Nat := 118140960795 + 1918257 * 2 ^ 59
def prefixEnd_1918257 : Nat := 4983230072969 + 3 ^ 40 * 1918257 * 2
def baseEnd_1918257 : Nat := 218886191078179232081245

theorem tailTrace_1918257 : CollatzResearch.WordTrace tailWord_1918257 prefixEnd_1918257 218886191078179232081245 := by
  unfold tailWord_1918257
  simp only [CollatzResearch.WordTrace]
  refine ⟨69964580611489976058169025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46643053740993317372112683 69964580611489976058169025)
  ·
    refine ⟨52473435458617482043626769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69964580611489976058169025 52473435458617482043626769)
    ·
      refine ⟨39355076593963111532720077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52473435458617482043626769 39355076593963111532720077)
      ·
        refine ⟨14758153722736166824770029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39355076593963111532720077 14758153722736166824770029)
        ·
          refine ⟨5534307646026062559288761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14758153722736166824770029 5534307646026062559288761)
          ·
            refine ⟨4150730734519546919466571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5534307646026062559288761 4150730734519546919466571)
            ·
              refine ⟨6226096101779320379199857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150730734519546919466571 6226096101779320379199857)
              ·
                refine ⟨4669572076334490284399893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6226096101779320379199857 4669572076334490284399893)
                ·
                  refine ⟨218886191078179232081245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4669572076334490284399893 218886191078179232081245)
                  ·
                    rfl

theorem cell22_1918257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_1918257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918257 prefixEnd_1918257 := by exact prefixLift 1918257
  have htrace : WordTrace (prefixWord ++ tailWord_1918257) baseStart_1918257 baseEnd_1918257 := by
    simpa [prefixWord, tailWord_1918257, baseEnd_1918257] using wordTrace_append hprefix tailTrace_1918257
  have hstable : (prefixWord ++ tailWord_1918257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918257).length < 2 ^ (prefixWord ++ tailWord_1918257).sum := by decide
  have hdescent : baseEnd_1918257 < baseStart_1918257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918272 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_1918272 : Nat := 118140960795 + 1918272 * 2 ^ 59
def prefixEnd_1918272 : Nat := 4983230072969 + 3 ^ 40 * 1918272 * 2
def baseEnd_1918272 : Nat := 656663708041082657118689

theorem tailTrace_1918272 : CollatzResearch.WordTrace tailWord_1918272 prefixEnd_1918272 656663708041082657118689 := by
  unfold tailWord_1918272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34982563853217816809982535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46643418470957089079976713 34982563853217816809982535)
  ·
    refine ⟨52473845779826725214973803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34982563853217816809982535 52473845779826725214973803)
    ·
      refine ⟨78710768669740087822460705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52473845779826725214973803 78710768669740087822460705)
      ·
        refine ⟨59033076502305065866845529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78710768669740087822460705 59033076502305065866845529)
        ·
          refine ⟨44274807376728799400134147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59033076502305065866845529 44274807376728799400134147)
          ·
            refine ⟨66412211065093199100201221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44274807376728799400134147 66412211065093199100201221)
            ·
              refine ⟨12452289574704974831287729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66412211065093199100201221 12452289574704974831287729)
              ·
                refine ⟨9339217181028731123465797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452289574704974831287729 9339217181028731123465797)
                ·
                  refine ⟨1751103221442887085649837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9339217181028731123465797 1751103221442887085649837)
                  ·
                    refine ⟨656663708041082657118689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751103221442887085649837 656663708041082657118689)
                    ·
                      rfl

theorem cell22_1918272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_1918272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918272 prefixEnd_1918272 := by exact prefixLift 1918272
  have htrace : WordTrace (prefixWord ++ tailWord_1918272) baseStart_1918272 baseEnd_1918272 := by
    simpa [prefixWord, tailWord_1918272, baseEnd_1918272] using wordTrace_append hprefix tailTrace_1918272
  have hstable : (prefixWord ++ tailWord_1918272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918272).length < 2 ^ (prefixWord ++ tailWord_1918272).sum := by decide
  have hdescent : baseEnd_1918272 < baseStart_1918272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918276 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1918276 : Nat := 118140960795 + 1918276 * 2 ^ 59
def prefixEnd_1918276 : Nat := 4983230072969 + 3 ^ 40 * 1918276 * 2
def baseEnd_1918276 : Nat := 656665077322827980018677

theorem tailTrace_1918276 : CollatzResearch.WordTrace tailWord_1918276 prefixEnd_1918276 656665077322827980018677 := by
  unfold tailWord_1918276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34982636799210571151555341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46643515732280761535407121 34982636799210571151555341)
  ·
    refine ⟨13118488799703964181833253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34982636799210571151555341 13118488799703964181833253)
    ·
      refine ⟨2459716649944493284093735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13118488799703964181833253 2459716649944493284093735)
      ·
        refine ⟨3689574974916739926140603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459716649944493284093735 3689574974916739926140603)
        ·
          refine ⟨5534362462375109889210905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689574974916739926140603 5534362462375109889210905)
          ·
            refine ⟨4150771846781332416908179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5534362462375109889210905 4150771846781332416908179)
            ·
              refine ⟨6226157770171998625362269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150771846781332416908179 6226157770171998625362269)
              ·
                refine ⟨2334809163814499484510851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6226157770171998625362269 2334809163814499484510851)
                ·
                  refine ⟨3502213745721749226766277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334809163814499484510851 3502213745721749226766277)
                  ·
                    refine ⟨656665077322827980018677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502213745721749226766277 656665077322827980018677)
                    ·
                      rfl

theorem cell22_1918276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1918276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918276 prefixEnd_1918276 := by exact prefixLift 1918276
  have htrace : WordTrace (prefixWord ++ tailWord_1918276) baseStart_1918276 baseEnd_1918276 := by
    simpa [prefixWord, tailWord_1918276, baseEnd_1918276] using wordTrace_append hprefix tailTrace_1918276
  have hstable : (prefixWord ++ tailWord_1918276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918276).length < 2 ^ (prefixWord ++ tailWord_1918276).sum := by decide
  have hdescent : baseEnd_1918276 < baseStart_1918276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918347 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 5]
def baseStart_1918347 : Nat := 118140960795 + 1918347 * 2 ^ 59
def prefixEnd_1918347 : Nat := 4983230072969 + 3 ^ 40 * 1918347 * 2
def baseEnd_1918347 : Nat := 218896460691269153831153

theorem tailTrace_1918347 : CollatzResearch.WordTrace tailWord_1918347 prefixEnd_1918347 218896460691269153831153 := by
  unfold tailWord_1918347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69967863181163921428945295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46645242120775947619296863 69967863181163921428945295)
  ·
    refine ⟨104951794771745882143417943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69967863181163921428945295 104951794771745882143417943)
    ·
      refine ⟨157427692157618823215126915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104951794771745882143417943 157427692157618823215126915)
      ·
        refine ⟨236141538236428234822690373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157427692157618823215126915 236141538236428234822690373)
        ·
          refine ⟨44276538419330294029254445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236141538236428234822690373 44276538419330294029254445)
          ·
            refine ⟨16603701907248860260970417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44276538419330294029254445 16603701907248860260970417)
            ·
              refine ⟨12452776430436645195727813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603701907248860260970417 12452776430436645195727813)
              ·
                refine ⟨2334895580706870974198965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12452776430436645195727813 2334895580706870974198965)
                ·
                  refine ⟨218896460691269153831153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334895580706870974198965 218896460691269153831153)
                  ·
                    rfl

theorem cell22_1918347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].length) (baseStart_1918347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918347 prefixEnd_1918347 := by exact prefixLift 1918347
  have htrace : WordTrace (prefixWord ++ tailWord_1918347) baseStart_1918347 baseEnd_1918347 := by
    simpa [prefixWord, tailWord_1918347, baseEnd_1918347] using wordTrace_append hprefix tailTrace_1918347
  have hstable : (prefixWord ++ tailWord_1918347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918347).length < 2 ^ (prefixWord ++ tailWord_1918347).sum := by decide
  have hdescent : baseEnd_1918347 < baseStart_1918347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918362 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1918362 : Nat := 118140960795 + 1918362 * 2 ^ 59
def prefixEnd_1918362 : Nat := 4983230072969 + 3 ^ 40 * 1918362 * 2
def baseEnd_1918362 : Nat := 656694516880352422368413

theorem tailTrace_1918362 : CollatzResearch.WordTrace tailWord_1918362 prefixEnd_1918362 656694516880352422368413 := by
  unfold tailWord_1918362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17492102569027394747685335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46645606850739719327160893 17492102569027394747685335)
  ·
    refine ⟨26238153853541092121528003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17492102569027394747685335 26238153853541092121528003)
    ·
      refine ⟨39357230780311638182292005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26238153853541092121528003 39357230780311638182292005)
      ·
        refine ⟨7379480771308432159179751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39357230780311638182292005 7379480771308432159179751)
        ·
          refine ⟨11069221156962648238769627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379480771308432159179751 11069221156962648238769627)
          ·
            refine ⟨16603831735443972358154441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11069221156962648238769627 16603831735443972358154441)
            ·
              refine ⟨12452873801582979268615831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603831735443972358154441 12452873801582979268615831)
              ·
                refine ⟨18679310702374468902923747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12452873801582979268615831 18679310702374468902923747)
                ·
                  refine ⟨28018966053561703354385621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18679310702374468902923747 28018966053561703354385621)
                  ·
                    refine ⟨656694516880352422368413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28018966053561703354385621 656694516880352422368413)
                    ·
                      rfl

theorem cell22_1918362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1918362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918362 prefixEnd_1918362 := by exact prefixLift 1918362
  have htrace : WordTrace (prefixWord ++ tailWord_1918362) baseStart_1918362 baseEnd_1918362 := by
    simpa [prefixWord, tailWord_1918362, baseEnd_1918362] using wordTrace_append hprefix tailTrace_1918362
  have hstable : (prefixWord ++ tailWord_1918362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918362).length < 2 ^ (prefixWord ++ tailWord_1918362).sum := by decide
  have hdescent : baseEnd_1918362 < baseStart_1918362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918407 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1918407 : Nat := 118140960795 + 1918407 * 2 ^ 59
def prefixEnd_1918407 : Nat := 4983230072969 + 3 ^ 40 * 1918407 * 2
def baseEnd_1918407 : Nat := 656709921299987304993275

theorem tailTrace_1918407 : CollatzResearch.WordTrace tailWord_1918407 prefixEnd_1918407 656709921299987304993275 := by
  unfold tailWord_1918407
  simp only [CollatzResearch.WordTrace]
  refine ⟨69970051560946551676129475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46646701040631034450752983 69970051560946551676129475)
  ·
    refine ⟨104955077341419827514194213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69970051560946551676129475 104955077341419827514194213)
    ·
      refine ⟨19679077001516217658911415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104955077341419827514194213 19679077001516217658911415)
      ·
        refine ⟨29518615502274326488367123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19679077001516217658911415 29518615502274326488367123)
        ·
          refine ⟨44277923253411489732550685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29518615502274326488367123 44277923253411489732550685)
          ·
            refine ⟨16604221220029308649706507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44277923253411489732550685 16604221220029308649706507)
            ·
              refine ⟨24906331830043962974559761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16604221220029308649706507 24906331830043962974559761)
              ·
                refine ⟨18679748872532972230919821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24906331830043962974559761 18679748872532972230919821)
                ·
                  refine ⟨7004905827199864586594933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18679748872532972230919821 7004905827199864586594933)
                  ·
                    refine ⟨656709921299987304993275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7004905827199864586594933 656709921299987304993275)
                    ·
                      rfl

theorem cell22_1918407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1918407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918407 prefixEnd_1918407 := by exact prefixLift 1918407
  have htrace : WordTrace (prefixWord ++ tailWord_1918407) baseStart_1918407 baseEnd_1918407 := by
    simpa [prefixWord, tailWord_1918407, baseEnd_1918407] using wordTrace_append hprefix tailTrace_1918407
  have hstable : (prefixWord ++ tailWord_1918407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918407).length < 2 ^ (prefixWord ++ tailWord_1918407).sum := by decide
  have hdescent : baseEnd_1918407 < baseStart_1918407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918439 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1918439 : Nat := 118140960795 + 1918439 * 2 ^ 59
def prefixEnd_1918439 : Nat := 4983230072969 + 3 ^ 40 * 1918439 * 2
def baseEnd_1918439 : Nat := 656720875553949888193177

theorem tailTrace_1918439 : CollatzResearch.WordTrace tailWord_1918439 prefixEnd_1918439 656720875553949888193177 := by
  unfold tailWord_1918439
  simp only [CollatzResearch.WordTrace]
  refine ⟨69971218696830621141294371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46647479131220414094196247 69971218696830621141294371)
  ·
    refine ⟨104956828045245931711941557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69971218696830621141294371 104956828045245931711941557)
    ·
      refine ⟨9839702629241806097994521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104956828045245931711941557 9839702629241806097994521)
      ·
        refine ⟨7379776971931354573495891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9839702629241806097994521 7379776971931354573495891)
        ·
          refine ⟨11069665457897031860243837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379776971931354573495891 11069665457897031860243837)
          ·
            refine ⟨4151124546711386947591439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11069665457897031860243837 4151124546711386947591439)
            ·
              refine ⟨6226686820067080421387159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151124546711386947591439 6226686820067080421387159)
              ·
                refine ⟨9340030230100620632080739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226686820067080421387159 9340030230100620632080739)
                ·
                  refine ⟨14010045345150930948121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340030230100620632080739 14010045345150930948121109)
                  ·
                    refine ⟨656720875553949888193177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14010045345150930948121109 656720875553949888193177)
                    ·
                      rfl

theorem cell22_1918439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1918439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918439 prefixEnd_1918439 := by exact prefixLift 1918439
  have htrace : WordTrace (prefixWord ++ tailWord_1918439) baseStart_1918439 baseEnd_1918439 := by
    simpa [prefixWord, tailWord_1918439, baseEnd_1918439] using wordTrace_append hprefix tailTrace_1918439
  have hstable : (prefixWord ++ tailWord_1918439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918439).length < 2 ^ (prefixWord ++ tailWord_1918439).sum := by decide
  have hdescent : baseEnd_1918439 < baseStart_1918439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918445 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_1918445 : Nat := 118140960795 + 1918445 * 2 ^ 59
def prefixEnd_1918445 : Nat := 4983230072969 + 3 ^ 40 * 1918445 * 2
def baseEnd_1918445 : Nat := 656722929476567872543159

theorem tailTrace_1918445 : CollatzResearch.WordTrace tailWord_1918445 prefixEnd_1918445 656722929476567872543159 := by
  unfold tailWord_1918445
  simp only [CollatzResearch.WordTrace]
  refine ⟨69971437534808884166012789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46647625023205922777341859 69971437534808884166012789)
  ·
    refine ⟨6559822268888332890563699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69971437534808884166012789 6559822268888332890563699)
    ·
      refine ⟨9839733403332499335845549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559822268888332890563699 9839733403332499335845549)
      ·
        refine ⟨3689900026249687250942081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9839733403332499335845549 3689900026249687250942081)
        ·
          refine ⟨2767425019687265438206561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689900026249687250942081 2767425019687265438206561)
          ·
            refine ⟨2075568764765449078654921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767425019687265438206561 2075568764765449078654921)
            ·
              refine ⟨1556676573574086808991191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075568764765449078654921 1556676573574086808991191)
              ·
                refine ⟨2335014860361130213486787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556676573574086808991191 2335014860361130213486787)
                ·
                  refine ⟨3502522290541695320230181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335014860361130213486787 3502522290541695320230181)
                  ·
                    refine ⟨656722929476567872543159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502522290541695320230181 656722929476567872543159)
                    ·
                      rfl

theorem cell22_1918445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_1918445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918445 prefixEnd_1918445 := by exact prefixLift 1918445
  have htrace : WordTrace (prefixWord ++ tailWord_1918445) baseStart_1918445 baseEnd_1918445 := by
    simpa [prefixWord, tailWord_1918445, baseEnd_1918445] using wordTrace_append hprefix tailTrace_1918445
  have hstable : (prefixWord ++ tailWord_1918445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918445).length < 2 ^ (prefixWord ++ tailWord_1918445).sum := by decide
  have hdescent : baseEnd_1918445 < baseStart_1918445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918454 : List Nat := [5, 1, 1, 1, 2, 3, 9]
def baseStart_1918454 : Nat := 118140960795 + 1918454 * 2 ^ 59
def prefixEnd_1918454 : Nat := 4983230072969 + 3 ^ 40 * 1918454 * 2
def baseEnd_1918454 : Nat := 24323185568907216632153

theorem tailTrace_1918454 : CollatzResearch.WordTrace tailWord_1918454 prefixEnd_1918454 24323185568907216632153 := by
  unfold tailWord_1918454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373235361986017418943151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46647843861184185802060277 4373235361986017418943151)
  ·
    refine ⟨6559853042979026128414727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373235361986017418943151 6559853042979026128414727)
    ·
      refine ⟨9839779564468539192622091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559853042979026128414727 9839779564468539192622091)
      ·
        refine ⟨14759669346702808788933137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839779564468539192622091 14759669346702808788933137)
        ·
          refine ⟨11069752010027106591699853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14759669346702808788933137 11069752010027106591699853)
          ·
            refine ⟨4151157003760164971887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11069752010027106591699853 4151157003760164971887445)
            ·
              refine ⟨24323185568907216632153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4151157003760164971887445 24323185568907216632153)
              ·
                rfl

theorem cell22_1918454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 9].length) (baseStart_1918454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918454 prefixEnd_1918454 := by exact prefixLift 1918454
  have htrace : WordTrace (prefixWord ++ tailWord_1918454) baseStart_1918454 baseEnd_1918454 := by
    simpa [prefixWord, tailWord_1918454, baseEnd_1918454] using wordTrace_append hprefix tailTrace_1918454
  have hstable : (prefixWord ++ tailWord_1918454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918454).length < 2 ^ (prefixWord ++ tailWord_1918454).sum := by decide
  have hdescent : baseEnd_1918454 < baseStart_1918454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918467 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_1918467 : Nat := 118140960795 + 1918467 * 2 ^ 59
def prefixEnd_1918467 : Nat := 4983230072969 + 3 ^ 40 * 1918467 * 2
def baseEnd_1918467 : Nat := 656730460526167148493091

theorem tailTrace_1918467 : CollatzResearch.WordTrace tailWord_1918467 prefixEnd_1918467 656730460526167148493091 := by
  unfold tailWord_1918467
  simp only [CollatzResearch.WordTrace]
  refine ⟨69972239940729181923313655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46648159960486121282209103 69972239940729181923313655)
  ·
    refine ⟨104958359911093772884970483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69972239940729181923313655 104958359911093772884970483)
    ·
      refine ⟨157437539866640659327455725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104958359911093772884970483 157437539866640659327455725)
      ·
        refine ⟨59039077449990247247795897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157437539866640659327455725 59039077449990247247795897)
        ·
          refine ⟨44279308087492685435846923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59039077449990247247795897 44279308087492685435846923)
          ·
            refine ⟨66418962131239028153770385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44279308087492685435846923 66418962131239028153770385)
            ·
              refine ⟨49814221598429271115327789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66418962131239028153770385 49814221598429271115327789)
              ·
                refine ⟨18680333099410976668247921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49814221598429271115327789 18680333099410976668247921)
                ·
                  refine ⟨14010249824558232501185941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18680333099410976668247921 14010249824558232501185941)
                  ·
                    refine ⟨656730460526167148493091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14010249824558232501185941 656730460526167148493091)
                    ·
                      rfl

theorem cell22_1918467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_1918467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918467 prefixEnd_1918467 := by exact prefixLift 1918467
  have htrace : WordTrace (prefixWord ++ tailWord_1918467) baseStart_1918467 baseEnd_1918467 := by
    simpa [prefixWord, tailWord_1918467, baseEnd_1918467] using wordTrace_append hprefix tailTrace_1918467
  have hstable : (prefixWord ++ tailWord_1918467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918467).length < 2 ^ (prefixWord ++ tailWord_1918467).sum := by decide
  have hdescent : baseEnd_1918467 < baseStart_1918467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918488 : List Nat := [2, 1, 2, 3, 5, 1, 2, 6]
def baseStart_1918488 : Nat := 118140960795 + 1918488 * 2 ^ 59
def prefixEnd_1918488 : Nat := 4983230072969 + 3 ^ 40 * 1918488 * 2
def baseEnd_1918488 : Nat := 72970849917258899302003

theorem tailTrace_1918488 : CollatzResearch.WordTrace tailWord_1918488 prefixEnd_1918488 72970849917258899302003 := by
  unfold tailWord_1918488
  simp only [CollatzResearch.WordTrace]
  refine ⟨34986502936826551254914059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46648670582435401673218745 34986502936826551254914059)
  ·
    refine ⟨52479754405239826882371089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34986502936826551254914059 52479754405239826882371089)
    ·
      refine ⟨39359815803929870161778317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52479754405239826882371089 39359815803929870161778317)
      ·
        refine ⟨14759930926473701310666869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39359815803929870161778317 14759930926473701310666869)
        ·
          refine ⟨1383743524356909497875019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14759930926473701310666869 1383743524356909497875019)
          ·
            refine ⟨2075615286535364246812529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383743524356909497875019 2075615286535364246812529)
            ·
              refine ⟨1556711464901523185109397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075615286535364246812529 1556711464901523185109397)
              ·
                refine ⟨72970849917258899302003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1556711464901523185109397 72970849917258899302003)
                ·
                  rfl

theorem cell22_1918488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_1918488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918488 prefixEnd_1918488 := by exact prefixLift 1918488
  have htrace : WordTrace (prefixWord ++ tailWord_1918488) baseStart_1918488 baseEnd_1918488 := by
    simpa [prefixWord, tailWord_1918488, baseEnd_1918488] using wordTrace_append hprefix tailTrace_1918488
  have hstable : (prefixWord ++ tailWord_1918488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918488).length < 2 ^ (prefixWord ++ tailWord_1918488).sum := by decide
  have hdescent : baseEnd_1918488 < baseStart_1918488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918494 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1918494 : Nat := 118140960795 + 1918494 * 2 ^ 59
def prefixEnd_1918494 : Nat := 4983230072969 + 3 ^ 40 * 1918494 * 2
def baseEnd_1918494 : Nat := 218913234392649359356003

theorem tailTrace_1918494 : CollatzResearch.WordTrace tailWord_1918494 prefixEnd_1918494 218913234392649359356003 := by
  unfold tailWord_1918494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746653088953920691818317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46648816474420910356364357 8746653088953920691818317)
  ·
    refine ⟨3279994908357720259431869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8746653088953920691818317 3279994908357720259431869)
    ·
      refine ⟨1229998090634145097286951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3279994908357720259431869 1229998090634145097286951)
      ·
        refine ⟨1844997135951217645930427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229998090634145097286951 1844997135951217645930427)
        ·
          refine ⟨2767495703926826468895641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844997135951217645930427 2767495703926826468895641)
          ·
            refine ⟨2075621777945119851671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767495703926826468895641 2075621777945119851671731)
            ·
              refine ⟨3113432666917679777507597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075621777945119851671731 3113432666917679777507597)
              ·
                refine ⟨1167537250094129916565349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3113432666917679777507597 1167537250094129916565349)
                ·
                  refine ⟨218913234392649359356003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167537250094129916565349 218913234392649359356003)
                  ·
                    rfl

theorem cell22_1918494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1918494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918494 prefixEnd_1918494 := by exact prefixLift 1918494
  have htrace : WordTrace (prefixWord ++ tailWord_1918494) baseStart_1918494 baseEnd_1918494 := by
    simpa [prefixWord, tailWord_1918494, baseEnd_1918494] using wordTrace_append hprefix tailTrace_1918494
  have hstable : (prefixWord ++ tailWord_1918494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918494).length < 2 ^ (prefixWord ++ tailWord_1918494).sum := by decide
  have hdescent : baseEnd_1918494 < baseStart_1918494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918520 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_1918520 : Nat := 118140960795 + 1918520 * 2 ^ 59
def prefixEnd_1918520 : Nat := 4983230072969 + 3 ^ 40 * 1918520 * 2
def baseEnd_1918520 : Nat := 656748603509292676917929

theorem tailTrace_1918520 : CollatzResearch.WordTrace tailWord_1918520 prefixEnd_1918520 656748603509292676917929 := by
  unfold tailWord_1918520
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987086504768585987496507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46649448673024781316662009 34987086504768585987496507)
  ·
    refine ⟨52480629757152878981244761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34987086504768585987496507 52480629757152878981244761)
    ·
      refine ⟨39360472317864659235933571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52480629757152878981244761 39360472317864659235933571)
      ·
        refine ⟨59040708476796988853900357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39360472317864659235933571 59040708476796988853900357)
        ·
          refine ⟨11070132839399435410106317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59040708476796988853900357 11070132839399435410106317)
          ·
            refine ⟨4151299814774788278789869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11070132839399435410106317 4151299814774788278789869)
            ·
              refine ⟨1556737430540545604546201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4151299814774788278789869 1556737430540545604546201)
              ·
                refine ⟨1167553072905409203409651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556737430540545604546201 1167553072905409203409651)
                ·
                  refine ⟨1751329609358113805114477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167553072905409203409651 1751329609358113805114477)
                  ·
                    refine ⟨656748603509292676917929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751329609358113805114477 656748603509292676917929)
                    ·
                      rfl

theorem cell22_1918520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_1918520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918520 prefixEnd_1918520 := by exact prefixLift 1918520
  have htrace : WordTrace (prefixWord ++ tailWord_1918520) baseStart_1918520 baseEnd_1918520 := by
    simpa [prefixWord, tailWord_1918520, baseEnd_1918520] using wordTrace_append hprefix tailTrace_1918520
  have hstable : (prefixWord ++ tailWord_1918520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918520).length < 2 ^ (prefixWord ++ tailWord_1918520).sum := by decide
  have hdescent : baseEnd_1918520 < baseStart_1918520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918546 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1918546 : Nat := 118140960795 + 1918546 * 2 ^ 59
def prefixEnd_1918546 : Nat := 4983230072969 + 3 ^ 40 * 1918546 * 2
def baseEnd_1918546 : Nat := 656757503840637275767849

theorem tailTrace_1918546 : CollatzResearch.WordTrace tailWord_1918546 prefixEnd_1918546 656757503840637275767849 := by
  unfold tailWord_1918546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493780326860744603859873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46650080871628652276959661 17493780326860744603859873)
  ·
    refine ⟨13120335245145558452894905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17493780326860744603859873 13120335245145558452894905)
    ·
      refine ⟨9840251433859168839671179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13120335245145558452894905 9840251433859168839671179)
      ·
        refine ⟨14760377150788753259506769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840251433859168839671179 14760377150788753259506769)
        ·
          refine ⟨11070282863091564944630077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14760377150788753259506769 11070282863091564944630077)
          ·
            refine ⟨4151356073659336854236279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11070282863091564944630077 4151356073659336854236279)
            ·
              refine ⟨6227034110489005281354419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151356073659336854236279 6227034110489005281354419)
              ·
                refine ⟨9340551165733507922031629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227034110489005281354419 9340551165733507922031629)
                ·
                  refine ⟨3502706687150065470761861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9340551165733507922031629 3502706687150065470761861)
                  ·
                    refine ⟨656757503840637275767849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502706687150065470761861 656757503840637275767849)
                    ·
                      rfl

theorem cell22_1918546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1918546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918546 prefixEnd_1918546 := by exact prefixLift 1918546
  have htrace : WordTrace (prefixWord ++ tailWord_1918546) baseStart_1918546 baseEnd_1918546 := by
    simpa [prefixWord, tailWord_1918546, baseEnd_1918546] using wordTrace_append hprefix tailTrace_1918546
  have hstable : (prefixWord ++ tailWord_1918546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918546).length < 2 ^ (prefixWord ++ tailWord_1918546).sum := by decide
  have hdescent : baseEnd_1918546 < baseStart_1918546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918561 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 4]
def baseStart_1918561 : Nat := 118140960795 + 1918561 * 2 ^ 59
def prefixEnd_1918561 : Nat := 4983230072969 + 3 ^ 40 * 1918561 * 2
def baseEnd_1918561 : Nat := 218920879549060745547601

theorem tailTrace_1918561 : CollatzResearch.WordTrace tailWord_1918561 prefixEnd_1918561 218920879549060745547601 := by
  unfold tailWord_1918561
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975668402388635977235537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46650445601592423984823691 69975668402388635977235537)
  ·
    refine ⟨52481751301791476982926653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69975668402388635977235537 52481751301791476982926653)
    ·
      refine ⟨19680656738171803868597495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52481751301791476982926653 19680656738171803868597495)
      ·
        refine ⟨29520985107257705802896243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19680656738171803868597495 29520985107257705802896243)
        ·
          refine ⟨44281477660886558704344365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29520985107257705802896243 44281477660886558704344365)
          ·
            refine ⟨16605554122832459514129137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44281477660886558704344365 16605554122832459514129137)
            ·
              refine ⟨12454165592124344635596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16605554122832459514129137 12454165592124344635596853)
              ·
                refine ⟨1167578024261657309587205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12454165592124344635596853 1167578024261657309587205)
                ·
                  refine ⟨218920879549060745547601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167578024261657309587205 218920879549060745547601)
                  ·
                    rfl

theorem cell22_1918561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_1918561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918561 prefixEnd_1918561 := by exact prefixLift 1918561
  have htrace : WordTrace (prefixWord ++ tailWord_1918561) baseStart_1918561 baseEnd_1918561 := by
    simpa [prefixWord, tailWord_1918561, baseEnd_1918561] using wordTrace_append hprefix tailTrace_1918561
  have hstable : (prefixWord ++ tailWord_1918561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918561).length < 2 ^ (prefixWord ++ tailWord_1918561).sum := by decide
  have hdescent : baseEnd_1918561 < baseStart_1918561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918563 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 1, 4]
def baseStart_1918563 : Nat := 118140960795 + 1918563 * 2 ^ 59
def prefixEnd_1918563 : Nat := 4983230072969 + 3 ^ 40 * 1918563 * 2
def baseEnd_1918563 : Nat := 656763323288054898092797

theorem tailTrace_1918563 : CollatzResearch.WordTrace tailWord_1918563 prefixEnd_1918563 656763323288054898092797 := by
  unfold tailWord_1918563
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975741348381390318808343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46650494232254260212538895 69975741348381390318808343)
  ·
    refine ⟨104963612022572085478212515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69975741348381390318808343 104963612022572085478212515)
    ·
      refine ⟨157445418033858128217318773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104963612022572085478212515 157445418033858128217318773)
      ·
        refine ⟨14760507940674199520373635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157445418033858128217318773 14760507940674199520373635)
        ·
          refine ⟨22140761911011299280560453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760507940674199520373635 22140761911011299280560453)
          ·
            refine ⟨4151392858314618615105085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22140761911011299280560453 4151392858314618615105085)
            ·
              refine ⟨1556772321867981980664407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4151392858314618615105085 1556772321867981980664407)
              ·
                refine ⟨2335158482801972970996611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556772321867981980664407 2335158482801972970996611)
                ·
                  refine ⟨3502737724202959456494917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335158482801972970996611 3502737724202959456494917)
                  ·
                    refine ⟨656763323288054898092797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3502737724202959456494917 656763323288054898092797)
                    ·
                      rfl

theorem cell22_1918563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 4].length) (baseStart_1918563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918563 prefixEnd_1918563 := by exact prefixLift 1918563
  have htrace : WordTrace (prefixWord ++ tailWord_1918563) baseStart_1918563 baseEnd_1918563 := by
    simpa [prefixWord, tailWord_1918563, baseEnd_1918563] using wordTrace_append hprefix tailTrace_1918563
  have hstable : (prefixWord ++ tailWord_1918563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918563).length < 2 ^ (prefixWord ++ tailWord_1918563).sum := by decide
  have hdescent : baseEnd_1918563 < baseStart_1918563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918578 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1918578 : Nat := 118140960795 + 1918578 * 2 ^ 59
def prefixEnd_1918578 : Nat := 4983230072969 + 3 ^ 40 * 1918578 * 2
def baseEnd_1918578 : Nat := 218922819364866619655917

theorem tailTrace_1918578 : CollatzResearch.WordTrace tailWord_1918578 prefixEnd_1918578 218922819364866619655917 := by
  unfold tailWord_1918578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494072110831761970151097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46650858962218031920402925 17494072110831761970151097)
  ·
    refine ⟨13120554083123821477613323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17494072110831761970151097 13120554083123821477613323)
    ·
      refine ⟨19680831124685732216419985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13120554083123821477613323 19680831124685732216419985)
      ·
        refine ⟨14760623343514299162314989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19680831124685732216419985 14760623343514299162314989)
        ·
          refine ⟨5535233753817862185868121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14760623343514299162314989 5535233753817862185868121)
          ·
            refine ⟨4151425315363396639401091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535233753817862185868121 4151425315363396639401091)
            ·
              refine ⟨6227137973045094959101637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151425315363396639401091 6227137973045094959101637)
              ·
                refine ⟨1167588369945955304831557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6227137973045094959101637 1167588369945955304831557)
                ·
                  refine ⟨218922819364866619655917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167588369945955304831557 218922819364866619655917)
                  ·
                    rfl

theorem cell22_1918578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1918578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918578 prefixEnd_1918578 := by exact prefixLift 1918578
  have htrace : WordTrace (prefixWord ++ tailWord_1918578) baseStart_1918578 baseEnd_1918578 := by
    simpa [prefixWord, tailWord_1918578, baseEnd_1918578] using wordTrace_append hprefix tailTrace_1918578
  have hstable : (prefixWord ++ tailWord_1918578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918578).length < 2 ^ (prefixWord ++ tailWord_1918578).sum := by decide
  have hdescent : baseEnd_1918578 < baseStart_1918578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918593 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1918593 : Nat := 118140960795 + 1918593 * 2 ^ 59
def prefixEnd_1918593 : Nat := 4983230072969 + 3 ^ 40 * 1918593 * 2
def baseEnd_1918593 : Nat := 656773592901144819842705

theorem tailTrace_1918593 : CollatzResearch.WordTrace tailWord_1918593 prefixEnd_1918593 656773592901144819842705 := by
  unfold tailWord_1918593
  simp only [CollatzResearch.WordTrace]
  refine ⟨69976835538272705442400433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46651223692181803628266955 69976835538272705442400433)
  ·
    refine ⟨52482626653704529081800325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69976835538272705442400433 52482626653704529081800325)
    ·
      refine ⟨9840492497569599202837561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52482626653704529081800325 9840492497569599202837561)
      ·
        refine ⟨7380369373177199402128171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840492497569599202837561 7380369373177199402128171)
        ·
          refine ⟨11070554059765799103192257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380369373177199402128171 11070554059765799103192257)
          ·
            refine ⟨8302915544824349327394193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11070554059765799103192257 8302915544824349327394193)
            ·
              refine ⟨6227186658618261995545645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302915544824349327394193 6227186658618261995545645)
              ·
                refine ⟨2335194996981848248329617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6227186658618261995545645 2335194996981848248329617)
                ·
                  refine ⟨1751396247736386186247213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335194996981848248329617 1751396247736386186247213)
                  ·
                    refine ⟨656773592901144819842705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751396247736386186247213 656773592901144819842705)
                    ·
                      rfl

theorem cell22_1918593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1918593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918593 prefixEnd_1918593 := by exact prefixLift 1918593
  have htrace : WordTrace (prefixWord ++ tailWord_1918593) baseStart_1918593 baseEnd_1918593 := by
    simpa [prefixWord, tailWord_1918593, baseEnd_1918593] using wordTrace_append hprefix tailTrace_1918593
  have hstable : (prefixWord ++ tailWord_1918593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918593).length < 2 ^ (prefixWord ++ tailWord_1918593).sum := by decide
  have hdescent : baseEnd_1918593 < baseStart_1918593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918621 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1918621 : Nat := 118140960795 + 1918621 * 2 ^ 59
def prefixEnd_1918621 : Nat := 4983230072969 + 3 ^ 40 * 1918621 * 2
def baseEnd_1918621 : Nat := 656783177873362080142619

theorem tailTrace_1918621 : CollatzResearch.WordTrace tailWord_1918621 prefixEnd_1918621 656783177873362080142619 := by
  unfold tailWord_1918621
  simp only [CollatzResearch.WordTrace]
  refine ⟨69977856782171266224419717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46651904521447510816279811 69977856782171266224419717)
  ·
    refine ⟨13120848146657112417078697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69977856782171266224419717 13120848146657112417078697)
    ·
      refine ⟨9840636109992834312809023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13120848146657112417078697 9840636109992834312809023)
      ·
        refine ⟨14760954164989251469213535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840636109992834312809023 14760954164989251469213535)
        ·
          refine ⟨22141431247483877203820303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760954164989251469213535 22141431247483877203820303)
          ·
            refine ⟨33212146871225815805730455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22141431247483877203820303 33212146871225815805730455)
            ·
              refine ⟨49818220306838723708595683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33212146871225815805730455 49818220306838723708595683)
              ·
                refine ⟨74727330460258085562893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49818220306838723708595683 74727330460258085562893525)
                ·
                  refine ⟨1751421807662298880380317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74727330460258085562893525 1751421807662298880380317)
                  ·
                    refine ⟨656783177873362080142619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751421807662298880380317 656783177873362080142619)
                    ·
                      rfl

theorem cell22_1918621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1918621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918621 prefixEnd_1918621 := by exact prefixLift 1918621
  have htrace : WordTrace (prefixWord ++ tailWord_1918621) baseStart_1918621 baseEnd_1918621 := by
    simpa [prefixWord, tailWord_1918621, baseEnd_1918621] using wordTrace_append hprefix tailTrace_1918621
  have hstable : (prefixWord ++ tailWord_1918621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918621).length < 2 ^ (prefixWord ++ tailWord_1918621).sum := by decide
  have hdescent : baseEnd_1918621 < baseStart_1918621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918740 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1918740 : Nat := 118140960795 + 1918740 * 2 ^ 59
def prefixEnd_1918740 : Nat := 4983230072969 + 3 ^ 40 * 1918740 * 2
def baseEnd_1918740 : Nat := 656823914005285436417255

theorem tailTrace_1918740 : CollatzResearch.WordTrace tailWord_1918740 prefixEnd_1918740 656823914005285436417255 := by
  unfold tailWord_1918740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34991098534370074774000837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46654798045826766365334449 34991098534370074774000837)
  ·
    refine ⟨6560830975194389020125157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34991098534370074774000837 6560830975194389020125157)
    ·
      refine ⟨1230155807848947941273467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6560830975194389020125157 1230155807848947941273467)
      ·
        refine ⟨1845233711773421911910201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230155807848947941273467 1845233711773421911910201)
        ·
          refine ⟨1383925283830066433932651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845233711773421911910201 1383925283830066433932651)
          ·
            refine ⟨2075887925745099650898977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383925283830066433932651 2075887925745099650898977)
            ·
              refine ⟨1556915944308824738174233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075887925745099650898977 1556915944308824738174233)
              ·
                refine ⟨1167686958231618553630675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556915944308824738174233 1167686958231618553630675)
                ·
                  refine ⟨1751530437347427830446013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167686958231618553630675 1751530437347427830446013)
                  ·
                    refine ⟨656823914005285436417255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751530437347427830446013 656823914005285436417255)
                    ·
                      rfl

theorem cell22_1918740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1918740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918740 prefixEnd_1918740 := by exact prefixLift 1918740
  have htrace : WordTrace (prefixWord ++ tailWord_1918740) baseStart_1918740 baseEnd_1918740 := by
    simpa [prefixWord, tailWord_1918740, baseEnd_1918740] using wordTrace_append hprefix tailTrace_1918740
  have hstable : (prefixWord ++ tailWord_1918740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918740).length < 2 ^ (prefixWord ++ tailWord_1918740).sum := by decide
  have hdescent : baseEnd_1918740 < baseStart_1918740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918743 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1918743 : Nat := 118140960795 + 1918743 * 2 ^ 59
def prefixEnd_1918743 : Nat := 4983230072969 + 3 ^ 40 * 1918743 * 2
def baseEnd_1918743 : Nat := 656824940966594428592245

theorem tailTrace_1918743 : CollatzResearch.WordTrace tailWord_1918743 prefixEnd_1918743 656824940966594428592245 := by
  unfold tailWord_1918743
  simp only [CollatzResearch.WordTrace]
  refine ⟨69982306487729281060360883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46654870991819520706907255 69982306487729281060360883)
  ·
    refine ⟨104973459731593921590541325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69982306487729281060360883 104973459731593921590541325)
    ·
      refine ⟨39365047399347720596452997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104973459731593921590541325 39365047399347720596452997)
      ·
        refine ⟨7380946387377697611834937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39365047399347720596452997 7380946387377697611834937)
        ·
          refine ⟨5535709790533273208876203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7380946387377697611834937 5535709790533273208876203)
          ·
            refine ⟨8303564685799909813314305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535709790533273208876203 8303564685799909813314305)
            ·
              refine ⟨6227673514349932359985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303564685799909813314305 6227673514349932359985729)
              ·
                refine ⟨4670755135762449269989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227673514349932359985729 4670755135762449269989297)
                ·
                  refine ⟨3503066351821836952491973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670755135762449269989297 3503066351821836952491973)
                  ·
                    refine ⟨656824940966594428592245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503066351821836952491973 656824940966594428592245)
                    ·
                      rfl

theorem cell22_1918743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1918743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918743 prefixEnd_1918743 := by exact prefixLift 1918743
  have htrace : WordTrace (prefixWord ++ tailWord_1918743) baseStart_1918743 baseEnd_1918743 := by
    simpa [prefixWord, tailWord_1918743, baseEnd_1918743] using wordTrace_append hprefix tailTrace_1918743
  have hstable : (prefixWord ++ tailWord_1918743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918743).length < 2 ^ (prefixWord ++ tailWord_1918743).sum := by decide
  have hdescent : baseEnd_1918743 < baseStart_1918743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918777 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_1918777 : Nat := 118140960795 + 1918777 * 2 ^ 59
def prefixEnd_1918777 : Nat := 4983230072969 + 3 ^ 40 * 1918777 * 2
def baseEnd_1918777 : Nat := 656836579861429673242141

theorem tailTrace_1918777 : CollatzResearch.WordTrace tailWord_1918777 prefixEnd_1918777 656836579861429673242141 := by
  unfold tailWord_1918777
  simp only [CollatzResearch.WordTrace]
  refine ⟨69983546569606104867098585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655697713070736578065723 69983546569606104867098585)
  ·
    refine ⟨52487659927204578650323939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69983546569606104867098585 52487659927204578650323939)
    ·
      refine ⟨78731489890806867975485909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52487659927204578650323939 78731489890806867975485909)
      ·
        refine ⟨1845269294315785968175451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78731489890806867975485909 1845269294315785968175451)
        ·
          refine ⟨2767903941473678952263177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845269294315785968175451 2767903941473678952263177)
          ·
            refine ⟨2075927956105259214197383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767903941473678952263177 2075927956105259214197383)
            ·
              refine ⟨3113891934157888821296075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075927956105259214197383 3113891934157888821296075)
              ·
                refine ⟨4670837901236833231944113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113891934157888821296075 4670837901236833231944113)
                ·
                  refine ⟨3503128425927624923958085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670837901236833231944113 3503128425927624923958085)
                  ·
                    refine ⟨656836579861429673242141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503128425927624923958085 656836579861429673242141)
                    ·
                      rfl

theorem cell22_1918777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_1918777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918777 prefixEnd_1918777 := by exact prefixLift 1918777
  have htrace : WordTrace (prefixWord ++ tailWord_1918777) baseStart_1918777 baseEnd_1918777 := by
    simpa [prefixWord, tailWord_1918777, baseEnd_1918777] using wordTrace_append hprefix tailTrace_1918777
  have hstable : (prefixWord ++ tailWord_1918777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918777).length < 2 ^ (prefixWord ++ tailWord_1918777).sum := by decide
  have hdescent : baseEnd_1918777 < baseStart_1918777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918946 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1918946 : Nat := 118140960795 + 1918946 * 2 ^ 59
def prefixEnd_1918946 : Nat := 4983230072969 + 3 ^ 40 * 1918946 * 2
def baseEnd_1918946 : Nat := 656894432015169565766623

theorem tailTrace_1918946 : CollatzResearch.WordTrace tailWord_1918946 prefixEnd_1918946 656894432015169565766623 := by
  unfold tailWord_1918946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497427626498461682500173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46659807003995897820000461 17497427626498461682500173)
  ·
    refine ⟨6561535359936923130937565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17497427626498461682500173 6561535359936923130937565)
    ·
      refine ⟨2460575759976346174101587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6561535359936923130937565 2460575759976346174101587)
      ·
        refine ⟨3690863639964519261152381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460575759976346174101587 3690863639964519261152381)
        ·
          refine ⟨1384073864986694722932143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3690863639964519261152381 1384073864986694722932143)
          ·
            refine ⟨2076110797480042084398215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384073864986694722932143 2076110797480042084398215)
            ·
              refine ⟨3114166196220063126597323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076110797480042084398215 3114166196220063126597323)
              ·
                refine ⟨4671249294330094689895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114166196220063126597323 4671249294330094689895985)
                ·
                  refine ⟨3503436970747571017421989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671249294330094689895985 3503436970747571017421989)
                  ·
                    refine ⟨656894432015169565766623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503436970747571017421989 656894432015169565766623)
                    ·
                      rfl

theorem cell22_1918946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1918946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1918946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1918946 prefixEnd_1918946 := by exact prefixLift 1918946
  have htrace : WordTrace (prefixWord ++ tailWord_1918946) baseStart_1918946 baseEnd_1918946 := by
    simpa [prefixWord, tailWord_1918946, baseEnd_1918946] using wordTrace_append hprefix tailTrace_1918946
  have hstable : (prefixWord ++ tailWord_1918946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918946).length < 2 ^ (prefixWord ++ tailWord_1918946).sum := by decide
  have hdescent : baseEnd_1918946 < baseStart_1918946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919002 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1919002 : Nat := 118140960795 + 1919002 * 2 ^ 59
def prefixEnd_1919002 : Nat := 4983230072969 + 3 ^ 40 * 1919002 * 2
def baseEnd_1919002 : Nat := 656913601959604086366451

theorem tailTrace_1919002 : CollatzResearch.WordTrace tailWord_1919002 prefixEnd_1919002 656913601959604086366451 := by
  unfold tailWord_1919002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497938248447742073509815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46661168662527312196026173 17497938248447742073509815)
  ·
    refine ⟨26246907372671613110264723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17497938248447742073509815 26246907372671613110264723)
    ·
      refine ⟨39370361059007419665397085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26246907372671613110264723 39370361059007419665397085)
      ·
        refine ⟨14763885397127782374523907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39370361059007419665397085 14763885397127782374523907)
        ·
          refine ⟨22145828095691673561785861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14763885397127782374523907 22145828095691673561785861)
          ·
            refine ⟨4152342767942188792834849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22145828095691673561785861 4152342767942188792834849)
            ·
              refine ⟨3114257075956641594626137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152342767942188792834849 3114257075956641594626137)
              ·
                refine ⟨2335692806967481195969603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3114257075956641594626137 2335692806967481195969603)
                ·
                  refine ⟨3503539210451221793954405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335692806967481195969603 3503539210451221793954405)
                  ·
                    refine ⟨656913601959604086366451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503539210451221793954405 656913601959604086366451)
                    ·
                      rfl

theorem cell22_1919002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1919002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919002 prefixEnd_1919002 := by exact prefixLift 1919002
  have htrace : WordTrace (prefixWord ++ tailWord_1919002) baseStart_1919002 baseEnd_1919002 := by
    simpa [prefixWord, tailWord_1919002, baseEnd_1919002] using wordTrace_append hprefix tailTrace_1919002
  have hstable : (prefixWord ++ tailWord_1919002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919002).length < 2 ^ (prefixWord ++ tailWord_1919002).sum := by decide
  have hdescent : baseEnd_1919002 < baseStart_1919002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_1919043 : Nat := 118140960795 + 1919043 * 2 ^ 59
def prefixEnd_1919043 : Nat := 4983230072969 + 3 ^ 40 * 1919043 * 2
def baseEnd_1919043 : Nat := 656927637097493646091325

theorem tailTrace_1919043 : CollatzResearch.WordTrace tailWord_1919043 prefixEnd_1919043 656927637097493646091325 := by
  unfold tailWord_1919043
  simp only [CollatzResearch.WordTrace]
  refine ⟨69993248386642432296281783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46662165591094954864187855 69993248386642432296281783)
  ·
    refine ⟨104989872579963648444422675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69993248386642432296281783 104989872579963648444422675)
    ·
      refine ⟨157484808869945472666634013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104989872579963648444422675 157484808869945472666634013)
      ·
        refine ⟨59056803326229552249987755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157484808869945472666634013 59056803326229552249987755)
        ·
          refine ⟨88585204989344328374981633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59056803326229552249987755 88585204989344328374981633)
          ·
            refine ⟨66438903742008246281236225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88585204989344328374981633 66438903742008246281236225)
            ·
              refine ⟨49829177806506184710927169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66438903742008246281236225 49829177806506184710927169)
              ·
                refine ⟨37371883354879638533195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49829177806506184710927169 37371883354879638533195377)
                ·
                  refine ⟨28028912516159728899896533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37371883354879638533195377 28028912516159728899896533)
                  ·
                    refine ⟨656927637097493646091325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28028912516159728899896533 656927637097493646091325)
                    ·
                      rfl

theorem cell22_1919043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_1919043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919043 prefixEnd_1919043 := by exact prefixLift 1919043
  have htrace : WordTrace (prefixWord ++ tailWord_1919043) baseStart_1919043 baseEnd_1919043 := by
    simpa [prefixWord, tailWord_1919043, baseEnd_1919043] using wordTrace_append hprefix tailTrace_1919043
  have hstable : (prefixWord ++ tailWord_1919043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919043).length < 2 ^ (prefixWord ++ tailWord_1919043).sum := by decide
  have hdescent : baseEnd_1919043 < baseStart_1919043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919120 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_1919120 : Nat := 118140960795 + 1919120 * 2 ^ 59
def prefixEnd_1919120 : Nat := 4983230072969 + 3 ^ 40 * 1919120 * 2
def baseEnd_1919120 : Nat := 656953995771091111916089

theorem tailTrace_1919120 : CollatzResearch.WordTrace tailWord_1919120 prefixEnd_1919120 656953995771091111916089 := by
  unfold tailWord_1919120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34998028403681737223417407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46664037871575649631223209 34998028403681737223417407)
  ·
    refine ⟨52497042605522605835126111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34998028403681737223417407 52497042605522605835126111)
    ·
      refine ⟨78745563908283908752689167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52497042605522605835126111 78745563908283908752689167)
      ·
        refine ⟨118118345862425863129033751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78745563908283908752689167 118118345862425863129033751)
        ·
          refine ⟨177177518793638794693550627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118118345862425863129033751 177177518793638794693550627)
          ·
            refine ⟨265766278190458192040325941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177177518793638794693550627 265766278190458192040325941)
            ·
              refine ⟨24915588580355455503780557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265766278190458192040325941 24915588580355455503780557)
              ·
                refine ⟨9343345717633295813917709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24915588580355455503780557 9343345717633295813917709)
                ·
                  refine ⟨3503754644112485930219141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9343345717633295813917709 3503754644112485930219141)
                  ·
                    refine ⟨656953995771091111916089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3503754644112485930219141 656953995771091111916089)
                    ·
                      rfl

theorem cell22_1919120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_1919120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919120 prefixEnd_1919120 := by exact prefixLift 1919120
  have htrace : WordTrace (prefixWord ++ tailWord_1919120) baseStart_1919120 baseEnd_1919120 := by
    simpa [prefixWord, tailWord_1919120, baseEnd_1919120] using wordTrace_append hprefix tailTrace_1919120
  have hstable : (prefixWord ++ tailWord_1919120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919120).length < 2 ^ (prefixWord ++ tailWord_1919120).sum := by decide
  have hdescent : baseEnd_1919120 < baseStart_1919120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919182 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1919182 : Nat := 118140960795 + 1919182 * 2 ^ 59
def prefixEnd_1919182 : Nat := 4983230072969 + 3 ^ 40 * 1919182 * 2
def baseEnd_1919182 : Nat := 656975219638143616865899

theorem tailTrace_1919182 : CollatzResearch.WordTrace tailWord_1919182 prefixEnd_1919182 656975219638143616865899 := by
  unfold tailWord_1919182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749789766642357379448975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46665545422092572690394533 8749789766642357379448975)
  ·
    refine ⟨13124684649963536069173463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749789766642357379448975 13124684649963536069173463)
    ·
      refine ⟨19687026974945304103760195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124684649963536069173463 19687026974945304103760195)
      ·
        refine ⟨29530540462417956155640293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687026974945304103760195 29530540462417956155640293)
        ·
          refine ⟨5536976336703366779182555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29530540462417956155640293 5536976336703366779182555)
          ·
            refine ⟨8305464505055050168773833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536976336703366779182555 8305464505055050168773833)
            ·
              refine ⟨6229098378791287626580375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305464505055050168773833 6229098378791287626580375)
              ·
                refine ⟨9343647568186931439870563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229098378791287626580375 9343647568186931439870563)
                ·
                  refine ⟨14015471352280397159805845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343647568186931439870563 14015471352280397159805845)
                  ·
                    refine ⟨656975219638143616865899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14015471352280397159805845 656975219638143616865899)
                    ·
                      rfl

theorem cell22_1919182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1919182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919182 prefixEnd_1919182 := by exact prefixLift 1919182
  have htrace : WordTrace (prefixWord ++ tailWord_1919182) baseStart_1919182 baseEnd_1919182 := by
    simpa [prefixWord, tailWord_1919182, baseEnd_1919182] using wordTrace_append hprefix tailTrace_1919182
  have hstable : (prefixWord ++ tailWord_1919182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919182).length < 2 ^ (prefixWord ++ tailWord_1919182).sum := by decide
  have hdescent : baseEnd_1919182 < baseStart_1919182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919186 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1919186 : Nat := 118140960795 + 1919186 * 2 ^ 59
def prefixEnd_1919186 : Nat := 4983230072969 + 3 ^ 40 * 1919186 * 2
def baseEnd_1919186 : Nat := 218992196306629646588629

theorem tailTrace_1919186 : CollatzResearch.WordTrace tailWord_1919186 prefixEnd_1919186 218992196306629646588629 := by
  unfold tailWord_1919186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499616006281091929684353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46665642683416245145824941 17499616006281091929684353)
  ·
    refine ⟨13124712004710818947263265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17499616006281091929684353 13124712004710818947263265)
    ·
      refine ⟨9843534003533114210447449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13124712004710818947263265 9843534003533114210447449)
      ·
        refine ⟨7382650502649835657835587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9843534003533114210447449 7382650502649835657835587)
        ·
          refine ⟨11073975753974753486753381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382650502649835657835587 11073975753974753486753381)
          ·
            refine ⟨2076370453870266278766259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11073975753974753486753381 2076370453870266278766259)
            ·
              refine ⟨3114555680805399418149389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076370453870266278766259 3114555680805399418149389)
              ·
                refine ⟨1167958380302024781806021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3114555680805399418149389 1167958380302024781806021)
                ·
                  refine ⟨218992196306629646588629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167958380302024781806021 218992196306629646588629)
                  ·
                    rfl

theorem cell22_1919186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1919186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919186 prefixEnd_1919186 := by exact prefixLift 1919186
  have htrace : WordTrace (prefixWord ++ tailWord_1919186) baseStart_1919186 baseEnd_1919186 := by
    simpa [prefixWord, tailWord_1919186, baseEnd_1919186] using wordTrace_append hprefix tailTrace_1919186
  have hstable : (prefixWord ++ tailWord_1919186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919186).length < 2 ^ (prefixWord ++ tailWord_1919186).sum := by decide
  have hdescent : baseEnd_1919186 < baseStart_1919186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919197 : List Nat := [1, 4, 3, 2, 1, 1, 10]
def baseStart_1919197 : Nat := 118140960795 + 1919197 * 2 ^ 59
def prefixEnd_1919197 : Nat := 4983230072969 + 3 ^ 40 * 1919197 * 2
def baseEnd_1919197 : Nat := 24332605720173651027439

theorem tailTrace_1919197 : CollatzResearch.WordTrace tailWord_1919197 prefixEnd_1919197 24332605720173651027439 := by
  unfold tailWord_1919197
  simp only [CollatzResearch.WordTrace]
  refine ⟨69998865228084516597387845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46665910152056344398258563 69998865228084516597387845)
  ·
    refine ⟨13124787230265846862010221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69998865228084516597387845 13124787230265846862010221)
    ·
      refine ⟨4921795211349692573253833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13124787230265846862010221 4921795211349692573253833)
      ·
        refine ⟨3691346408512269429940375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4921795211349692573253833 3691346408512269429940375)
        ·
          refine ⟨5537019612768404144910563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691346408512269429940375 5537019612768404144910563)
          ·
            refine ⟨8305529419152606217365845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537019612768404144910563 8305529419152606217365845)
            ·
              refine ⟨24332605720173651027439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8305529419152606217365845 24332605720173651027439)
              ·
                rfl

theorem cell22_1919197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 10].length) (baseStart_1919197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919197 prefixEnd_1919197 := by exact prefixLift 1919197
  have htrace : WordTrace (prefixWord ++ tailWord_1919197) baseStart_1919197 baseEnd_1919197 := by
    simpa [prefixWord, tailWord_1919197, baseEnd_1919197] using wordTrace_append hprefix tailTrace_1919197
  have hstable : (prefixWord ++ tailWord_1919197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919197).length < 2 ^ (prefixWord ++ tailWord_1919197).sum := by decide
  have hdescent : baseEnd_1919197 < baseStart_1919197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919203 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 4]
def baseStart_1919203 : Nat := 118140960795 + 1919203 * 2 ^ 59
def prefixEnd_1919203 : Nat := 4983230072969 + 3 ^ 40 * 1919203 * 2
def baseEnd_1919203 : Nat := 218994136122435520696945

theorem tailTrace_1919203 : CollatzResearch.WordTrace tailWord_1919203 prefixEnd_1919203 218994136122435520696945 := by
  unfold tailWord_1919203
  simp only [CollatzResearch.WordTrace]
  refine ⟨69999084066062779622106263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46666056044041853081404175 69999084066062779622106263)
  ·
    refine ⟨104998626099094169433159395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69999084066062779622106263 104998626099094169433159395)
    ·
      refine ⟨157497939148641254149739093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104998626099094169433159395 157497939148641254149739093)
      ·
        refine ⟨1845678974398139697067255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 157497939148641254149739093 1845678974398139697067255)
        ·
          refine ⟨2768518461597209545600883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845678974398139697067255 2768518461597209545600883)
          ·
            refine ⟨4152777692395814318401325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768518461597209545600883 4152777692395814318401325)
            ·
              refine ⟨1557291634648430369400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4152777692395814318401325 1557291634648430369400497)
              ·
                refine ⟨1167968725986322777050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557291634648430369400497 1167968725986322777050373)
                ·
                  refine ⟨218994136122435520696945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167968725986322777050373 218994136122435520696945)
                  ·
                    rfl

theorem cell22_1919203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 4].length) (baseStart_1919203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919203 prefixEnd_1919203 := by exact prefixLift 1919203
  have htrace : WordTrace (prefixWord ++ tailWord_1919203) baseStart_1919203 baseEnd_1919203 := by
    simpa [prefixWord, tailWord_1919203, baseEnd_1919203] using wordTrace_append hprefix tailTrace_1919203
  have hstable : (prefixWord ++ tailWord_1919203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919203).length < 2 ^ (prefixWord ++ tailWord_1919203).sum := by decide
  have hdescent : baseEnd_1919203 < baseStart_1919203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919218 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_1919218 : Nat := 118140960795 + 1919218 * 2 ^ 59
def prefixEnd_1919218 : Nat := 4983230072969 + 3 ^ 40 * 1919218 * 2
def baseEnd_1919218 : Nat := 656987543173851522965789

theorem tailTrace_1919218 : CollatzResearch.WordTrace tailWord_1919218 prefixEnd_1919218 656987543173851522965789 := by
  unfold tailWord_1919218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499907790252109295975577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46666420774005624789268205 17499907790252109295975577)
  ·
    refine ⟨13124930842689081971981683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17499907790252109295975577 13124930842689081971981683)
    ·
      refine ⟨19687396264033622957972525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124930842689081971981683 19687396264033622957972525)
      ·
        refine ⟨7382773599012608609239697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19687396264033622957972525 7382773599012608609239697)
        ·
          refine ⟨5537080199259456456929773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382773599012608609239697 5537080199259456456929773)
          ·
            refine ⟨2076405074722296171348665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5537080199259456456929773 2076405074722296171348665)
            ·
              refine ⟨1557303806041722128511499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076405074722296171348665 1557303806041722128511499)
              ·
                refine ⟨2335955709062583192767249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557303806041722128511499 2335955709062583192767249)
                ·
                  refine ⟨1751966781796937394575437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335955709062583192767249 1751966781796937394575437)
                  ·
                    refine ⟨656987543173851522965789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751966781796937394575437 656987543173851522965789)
                    ·
                      rfl

theorem cell22_1919218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_1919218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919218 prefixEnd_1919218 := by exact prefixLift 1919218
  have htrace : WordTrace (prefixWord ++ tailWord_1919218) baseStart_1919218 baseEnd_1919218 := by
    simpa [prefixWord, tailWord_1919218, baseEnd_1919218] using wordTrace_append hprefix tailTrace_1919218
  have hstable : (prefixWord ++ tailWord_1919218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919218).length < 2 ^ (prefixWord ++ tailWord_1919218).sum := by decide
  have hdescent : baseEnd_1919218 < baseStart_1919218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919225 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 9]
def baseStart_1919225 : Nat := 118140960795 + 1919225 * 2 ^ 59
def prefixEnd_1919225 : Nat := 4983230072969 + 3 ^ 40 * 1919225 * 2
def baseEnd_1919225 : Nat := 218996646472301946013589

theorem tailTrace_1919225 : CollatzResearch.WordTrace tailWord_1919225 prefixEnd_1919225 218996646472301946013589 := by
  unfold tailWord_1919225
  simp only [CollatzResearch.WordTrace]
  refine ⟨69999886471983077379407129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46666590981322051586271419 69999886471983077379407129)
  ·
    refine ⟨52499914853987308034555347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69999886471983077379407129 52499914853987308034555347)
    ·
      refine ⟨78749872280980962051833021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52499914853987308034555347 78749872280980962051833021)
      ·
        refine ⟨29531202105367860769437383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78749872280980962051833021 29531202105367860769437383)
        ·
          refine ⟨44296803158051791154156075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531202105367860769437383 44296803158051791154156075)
          ·
            refine ⟨66445204737077686731234113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44296803158051791154156075 66445204737077686731234113)
            ·
              refine ⟨49833903552808265048425585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66445204737077686731234113 49833903552808265048425585)
              ·
                refine ⟨37375427664606198786319189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49833903552808265048425585 37375427664606198786319189)
                ·
                  refine ⟨218996646472301946013589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37375427664606198786319189 218996646472301946013589)
                  ·
                    rfl

theorem cell22_1919225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_1919225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919225 prefixEnd_1919225 := by exact prefixLift 1919225
  have htrace : WordTrace (prefixWord ++ tailWord_1919225) baseStart_1919225 baseEnd_1919225 := by
    simpa [prefixWord, tailWord_1919225, baseEnd_1919225] using wordTrace_append hprefix tailTrace_1919225
  have hstable : (prefixWord ++ tailWord_1919225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919225).length < 2 ^ (prefixWord ++ tailWord_1919225).sum := by decide
  have hdescent : baseEnd_1919225 < baseStart_1919225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919246 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_1919246 : Nat := 118140960795 + 1919246 * 2 ^ 59
def prefixEnd_1919246 : Nat := 4983230072969 + 3 ^ 40 * 1919246 * 2
def baseEnd_1919246 : Nat := 656997128146068783265703

theorem tailTrace_1919246 : CollatzResearch.WordTrace tailWord_1919246 prefixEnd_1919246 656997128146068783265703 := by
  unfold tailWord_1919246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750081550613374745740199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46667101603271331977281061 8750081550613374745740199)
  ·
    refine ⟨13125122325920062118610299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750081550613374745740199 13125122325920062118610299)
    ·
      refine ⟨19687683488880093177915449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125122325920062118610299 19687683488880093177915449)
      ·
        refine ⟨14765762616660069883436587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19687683488880093177915449 14765762616660069883436587)
        ·
          refine ⟨22148643924990104825154881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14765762616660069883436587 22148643924990104825154881)
          ·
            refine ⟨16611482943742578618866161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22148643924990104825154881 16611482943742578618866161)
            ·
              refine ⟨12458612207806933964149621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16611482943742578618866161 12458612207806933964149621)
              ·
                refine ⟨1167994894481900059139027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12458612207806933964149621 1167994894481900059139027)
                ·
                  refine ⟨1751992341722850088708541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167994894481900059139027 1751992341722850088708541)
                  ·
                    refine ⟨656997128146068783265703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751992341722850088708541 656997128146068783265703)
                    ·
                      rfl

theorem cell22_1919246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_1919246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919246 prefixEnd_1919246 := by exact prefixLift 1919246
  have htrace : WordTrace (prefixWord ++ tailWord_1919246) baseStart_1919246 baseEnd_1919246 := by
    simpa [prefixWord, tailWord_1919246, baseEnd_1919246] using wordTrace_append hprefix tailTrace_1919246
  have hstable : (prefixWord ++ tailWord_1919246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919246).length < 2 ^ (prefixWord ++ tailWord_1919246).sum := by decide
  have hdescent : baseEnd_1919246 < baseStart_1919246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919263 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 1, 3]
def baseStart_1919263 : Nat := 118140960795 + 1919263 * 2 ^ 59
def prefixEnd_1919263 : Nat := 4983230072969 + 3 ^ 40 * 1919263 * 2
def baseEnd_1919263 : Nat := 657002947593486405590651

theorem tailTrace_1919263 : CollatzResearch.WordTrace tailWord_1919263 prefixEnd_1919263 657002947593486405590651 := by
  unfold tailWord_1919263
  simp only [CollatzResearch.WordTrace]
  refine ⟨70001272445845409869290443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46667514963896939912860295 70001272445845409869290443)
  ·
    refine ⟨105001908668768114803935665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70001272445845409869290443 105001908668768114803935665)
    ·
      refine ⟨78751431501576086102951749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105001908668768114803935665 78751431501576086102951749)
      ·
        refine ⟨14765893406545516144303453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78751431501576086102951749 14765893406545516144303453)
        ·
          refine ⟨5537210027454568554113795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14765893406545516144303453 5537210027454568554113795)
          ·
            refine ⟨8305815041181852831170693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537210027454568554113795 8305815041181852831170693)
            ·
              refine ⟨1557340320221597405844505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8305815041181852831170693 1557340320221597405844505)
              ·
                refine ⟨1168005240166198054383379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557340320221597405844505 1168005240166198054383379)
                ·
                  refine ⟨1752007860249297081575069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168005240166198054383379 1752007860249297081575069)
                  ·
                    refine ⟨657002947593486405590651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752007860249297081575069 657002947593486405590651)
                    ·
                      rfl

theorem cell22_1919263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_1919263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919263 prefixEnd_1919263 := by exact prefixLift 1919263
  have htrace : WordTrace (prefixWord ++ tailWord_1919263) baseStart_1919263 baseEnd_1919263 := by
    simpa [prefixWord, tailWord_1919263, baseEnd_1919263] using wordTrace_append hprefix tailTrace_1919263
  have hstable : (prefixWord ++ tailWord_1919263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919263).length < 2 ^ (prefixWord ++ tailWord_1919263).sum := by decide
  have hdescent : baseEnd_1919263 < baseStart_1919263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919289 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_1919289 : Nat := 118140960795 + 1919289 * 2 ^ 59
def prefixEnd_1919289 : Nat := 4983230072969 + 3 ^ 40 * 1919289 * 2
def baseEnd_1919289 : Nat := 657011847924831004440571

theorem tailTrace_1919289 : CollatzResearch.WordTrace tailWord_1919289 prefixEnd_1919289 657011847924831004440571 := by
  unfold tailWord_1919289
  simp only [CollatzResearch.WordTrace]
  refine ⟨70002220743751216309736921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46668147162500810873157947 70002220743751216309736921)
  ·
    refine ⟨52501665557813412232302691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70002220743751216309736921 52501665557813412232302691)
    ·
      refine ⟨78752498336720118348454037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52501665557813412232302691 78752498336720118348454037)
      ·
        refine ⟨3691523359533755547583783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78752498336720118348454037 3691523359533755547583783)
        ·
          refine ⟨5537285039300633321375675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691523359533755547583783 5537285039300633321375675)
          ·
            refine ⟨8305927558950949982063513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537285039300633321375675 8305927558950949982063513)
            ·
              refine ⟨6229445669213212486547635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305927558950949982063513 6229445669213212486547635)
              ·
                refine ⟨9344168503819818729821453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229445669213212486547635 9344168503819818729821453)
                ·
                  refine ⟨3504063188932432023683045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9344168503819818729821453 3504063188932432023683045)
                  ·
                    refine ⟨657011847924831004440571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3504063188932432023683045 657011847924831004440571)
                    ·
                      rfl

theorem cell22_1919289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_1919289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919289 prefixEnd_1919289 := by exact prefixLift 1919289
  have htrace : WordTrace (prefixWord ++ tailWord_1919289) baseStart_1919289 baseEnd_1919289 := by
    simpa [prefixWord, tailWord_1919289, baseEnd_1919289] using wordTrace_append hprefix tailTrace_1919289
  have hstable : (prefixWord ++ tailWord_1919289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919289).length < 2 ^ (prefixWord ++ tailWord_1919289).sum := by decide
  have hdescent : baseEnd_1919289 < baseStart_1919289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919304 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_1919304 : Nat := 118140960795 + 1919304 * 2 ^ 59
def prefixEnd_1919304 : Nat := 4983230072969 + 3 ^ 40 * 1919304 * 2
def baseEnd_1919304 : Nat := 219005660910458655105175

theorem tailTrace_1919304 : CollatzResearch.WordTrace tailWord_1919304 prefixEnd_1919304 219005660910458655105175 := by
  unfold tailWord_1919304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001383919348436935766483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46668511892464582581021977 35001383919348436935766483)
  ·
    refine ⟨52502075879022655403649725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35001383919348436935766483 52502075879022655403649725)
    ·
      refine ⟨19688278454633495776368647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52502075879022655403649725 19688278454633495776368647)
      ·
        refine ⟨29532417681950243664552971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19688278454633495776368647 29532417681950243664552971)
        ·
          refine ⟨44298626522925365496829457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29532417681950243664552971 44298626522925365496829457)
          ·
            refine ⟨33223969892194024122622093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44298626522925365496829457 33223969892194024122622093)
            ·
              refine ⟨12458988709572759045983285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33223969892194024122622093 12458988709572759045983285)
              ·
                refine ⟨1168030191522446160560933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12458988709572759045983285 1168030191522446160560933)
                ·
                  refine ⟨219005660910458655105175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168030191522446160560933 219005660910458655105175)
                  ·
                    rfl

theorem cell22_1919304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_1919304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919304 prefixEnd_1919304 := by exact prefixLift 1919304
  have htrace : WordTrace (prefixWord ++ tailWord_1919304) baseStart_1919304 baseEnd_1919304 := by
    simpa [prefixWord, tailWord_1919304, baseEnd_1919304] using wordTrace_append hprefix tailTrace_1919304
  have hstable : (prefixWord ++ tailWord_1919304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919304).length < 2 ^ (prefixWord ++ tailWord_1919304).sum := by decide
  have hdescent : baseEnd_1919304 < baseStart_1919304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919319 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 4, 3]
def baseStart_1919319 : Nat := 118140960795 + 1919319 * 2 ^ 59
def prefixEnd_1919319 : Nat := 4983230072969 + 3 ^ 40 * 1919319 * 2
def baseEnd_1919319 : Nat := 657022117537920926190479

theorem tailTrace_1919319 : CollatzResearch.WordTrace tailWord_1919319 prefixEnd_1919319 657022117537920926190479 := by
  unfold tailWord_1919319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70003314933642531433329011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46668876622428354288886007 70003314933642531433329011)
  ·
    refine ⟨105004972400463797149993517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70003314933642531433329011 105004972400463797149993517)
    ·
      refine ⟨39376864650173923931247569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105004972400463797149993517 39376864650173923931247569)
      ·
        refine ⟨29532648487630442948435677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39376864650173923931247569 29532648487630442948435677)
        ·
          refine ⟨11074743182861416105663379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29532648487630442948435677 11074743182861416105663379)
          ·
            refine ⟨16612114774292124158495069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074743182861416105663379 16612114774292124158495069)
            ·
              refine ⟨6229543040359546559435651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16612114774292124158495069 6229543040359546559435651)
              ·
                refine ⟨9344314560539319839153477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229543040359546559435651 9344314560539319839153477)
                ·
                  refine ⟨1752058980101122469841277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9344314560539319839153477 1752058980101122469841277)
                  ·
                    refine ⟨657022117537920926190479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752058980101122469841277 657022117537920926190479)
                    ·
                      rfl

theorem cell22_1919319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_1919319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919319 prefixEnd_1919319 := by exact prefixLift 1919319
  have htrace : WordTrace (prefixWord ++ tailWord_1919319) baseStart_1919319 baseEnd_1919319 := by
    simpa [prefixWord, tailWord_1919319, baseEnd_1919319] using wordTrace_append hprefix tailTrace_1919319
  have hstable : (prefixWord ++ tailWord_1919319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919319).length < 2 ^ (prefixWord ++ tailWord_1919319).sum := by decide
  have hdescent : baseEnd_1919319 < baseStart_1919319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919332 : List Nat := [2, 3, 1, 1, 3, 1, 2, 9]
def baseStart_1919332 : Nat := 118140960795 + 1919332 * 2 ^ 59
def prefixEnd_1919332 : Nat := 4983230072969 + 3 ^ 40 * 1919332 * 2
def baseEnd_1919332 : Nat := 73002951967065913957271

theorem tailTrace_1919332 : CollatzResearch.WordTrace tailWord_1919332 prefixEnd_1919332 73002951967065913957271 := by
  unfold tailWord_1919332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001894541297717326776125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46669192721730289769034833 35001894541297717326776125)
  ·
    refine ⟨13125710452986643997541047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35001894541297717326776125 13125710452986643997541047)
    ·
      refine ⟨19688565679479965996311571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125710452986643997541047 19688565679479965996311571)
      ·
        refine ⟨29532848519219948994467357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19688565679479965996311571 29532848519219948994467357)
        ·
          refine ⟨11074818194707480872925259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29532848519219948994467357 11074818194707480872925259)
          ·
            refine ⟨16612227292061221309387889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074818194707480872925259 16612227292061221309387889)
            ·
              refine ⟨12459170469045915982040917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16612227292061221309387889 12459170469045915982040917)
              ·
                refine ⟨73002951967065913957271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12459170469045915982040917 73002951967065913957271)
                ·
                  rfl

theorem cell22_1919332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_1919332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919332 prefixEnd_1919332 := by exact prefixLift 1919332
  have htrace : WordTrace (prefixWord ++ tailWord_1919332) baseStart_1919332 baseEnd_1919332 := by
    simpa [prefixWord, tailWord_1919332, baseEnd_1919332] using wordTrace_append hprefix tailTrace_1919332
  have hstable : (prefixWord ++ tailWord_1919332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919332).length < 2 ^ (prefixWord ++ tailWord_1919332).sum := by decide
  have hdescent : baseEnd_1919332 < baseStart_1919332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919336 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1919336 : Nat := 118140960795 + 1919336 * 2 ^ 59
def prefixEnd_1919336 : Nat := 4983230072969 + 3 ^ 40 * 1919336 * 2
def baseEnd_1919336 : Nat := 657027936985338548515427

theorem tailTrace_1919336 : CollatzResearch.WordTrace tailWord_1919336 prefixEnd_1919336 657027936985338548515427 := by
  unfold tailWord_1919336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001967487290471668348931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46669289983053962224465241 35001967487290471668348931)
  ·
    refine ⟨52502951230935707502523397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35001967487290471668348931 52502951230935707502523397)
    ·
      refine ⟨9844303355800445156723137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52502951230935707502523397 9844303355800445156723137)
      ·
        refine ⟨7383227516850333867542353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844303355800445156723137 7383227516850333867542353)
        ·
          refine ⟨5537420637637750400656765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7383227516850333867542353 5537420637637750400656765)
          ·
            refine ⟨2076532739114156400246287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5537420637637750400656765 2076532739114156400246287)
            ·
              refine ⟨3114799108671234600369431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076532739114156400246287 3114799108671234600369431)
              ·
                refine ⟨4672198663006851900554147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114799108671234600369431 4672198663006851900554147)
                ·
                  refine ⟨7008297994510277850831221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672198663006851900554147 7008297994510277850831221)
                  ·
                    refine ⟨657027936985338548515427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7008297994510277850831221 657027936985338548515427)
                    ·
                      rfl

theorem cell22_1919336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1919336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919336 prefixEnd_1919336 := by exact prefixLift 1919336
  have htrace : WordTrace (prefixWord ++ tailWord_1919336) baseStart_1919336 baseEnd_1919336 := by
    simpa [prefixWord, tailWord_1919336, baseEnd_1919336] using wordTrace_append hprefix tailTrace_1919336
  have hstable : (prefixWord ++ tailWord_1919336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919336).length < 2 ^ (prefixWord ++ tailWord_1919336).sum := by decide
  have hdescent : baseEnd_1919336 < baseStart_1919336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919349 : List Nat := [1, 3, 4, 1, 2, 2, 1, 8]
def baseStart_1919349 : Nat := 118140960795 + 1919349 * 2 ^ 59
def prefixEnd_1919349 : Nat := 4983230072969 + 3 ^ 40 * 1919349 * 2
def baseEnd_1919349 : Nat := 73003598572334538660043

theorem tailTrace_1919349 : CollatzResearch.WordTrace tailWord_1919349 prefixEnd_1919349 73003598572334538660043 := by
  unfold tailWord_1919349
  simp only [CollatzResearch.WordTrace]
  refine ⟨70004409123533846556921101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46669606082355897704614067 70004409123533846556921101)
  ·
    refine ⟨26251653421325192458845413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70004409123533846556921101 26251653421325192458845413)
    ·
      refine ⟨4922185016498473586033515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26251653421325192458845413 4922185016498473586033515)
      ·
        refine ⟨7383277524747710379050273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922185016498473586033515 7383277524747710379050273)
        ·
          refine ⟨5537458143560782784287705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7383277524747710379050273 5537458143560782784287705)
          ·
            refine ⟨4153093607670587088215779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537458143560782784287705 4153093607670587088215779)
            ·
              refine ⟨6229640411505880632323669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153093607670587088215779 6229640411505880632323669)
              ·
                refine ⟨73003598572334538660043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6229640411505880632323669 73003598572334538660043)
                ·
                  rfl

theorem cell22_1919349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 8].length) (baseStart_1919349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919349 prefixEnd_1919349 := by exact prefixLift 1919349
  have htrace : WordTrace (prefixWord ++ tailWord_1919349) baseStart_1919349 baseEnd_1919349 := by
    simpa [prefixWord, tailWord_1919349, baseEnd_1919349] using wordTrace_append hprefix tailTrace_1919349
  have hstable : (prefixWord ++ tailWord_1919349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919349).length < 2 ^ (prefixWord ++ tailWord_1919349).sum := by decide
  have hdescent : baseEnd_1919349 < baseStart_1919349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919428 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1919428 : Nat := 118140960795 + 1919428 * 2 ^ 59
def prefixEnd_1919428 : Nat := 4983230072969 + 3 ^ 40 * 1919428 * 2
def baseEnd_1919428 : Nat := 219019810155160325071715

theorem tailTrace_1919428 : CollatzResearch.WordTrace tailWord_1919428 prefixEnd_1919428 219019810155160325071715 := by
  unfold tailWord_1919428
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003645245123821524523469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46671526993498428699364625 35003645245123821524523469)
  ·
    refine ⟨13126366966921433071696301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35003645245123821524523469 13126366966921433071696301)
    ·
      refine ⟨4922387612595537401886113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13126366966921433071696301 4922387612595537401886113)
      ·
        refine ⟨3691790709446653051414585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922387612595537401886113 3691790709446653051414585)
        ·
          refine ⟨2768843032084989788560939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3691790709446653051414585 2768843032084989788560939)
          ·
            refine ⟨4153264548127484682841409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768843032084989788560939 4153264548127484682841409)
            ·
              refine ⟨3114948411095613512131057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153264548127484682841409 3114948411095613512131057)
              ·
                refine ⟨2336211308321710134098293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3114948411095613512131057 2336211308321710134098293)
                ·
                  refine ⟨219019810155160325071715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2336211308321710134098293 219019810155160325071715)
                  ·
                    rfl

theorem cell22_1919428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1919428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919428 prefixEnd_1919428 := by exact prefixLift 1919428
  have htrace : WordTrace (prefixWord ++ tailWord_1919428) baseStart_1919428 baseEnd_1919428 := by
    simpa [prefixWord, tailWord_1919428, baseEnd_1919428] using wordTrace_append hprefix tailTrace_1919428
  have hstable : (prefixWord ++ tailWord_1919428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919428).length < 2 ^ (prefixWord ++ tailWord_1919428).sum := by decide
  have hdescent : baseEnd_1919428 < baseStart_1919428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919514 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1919514 : Nat := 118140960795 + 1919514 * 2 ^ 59
def prefixEnd_1919514 : Nat := 4983230072969 + 3 ^ 40 * 1919514 * 2
def baseEnd_1919514 : Nat := 657088870023005417564881

theorem tailTrace_1919514 : CollatzResearch.WordTrace tailWord_1919514 prefixEnd_1919514 657088870023005417564881 := by
  unfold tailWord_1919514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502606791984019934169399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46673618111957386491118397 17502606791984019934169399)
  ·
    refine ⟨26253910187976029901254099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17502606791984019934169399 26253910187976029901254099)
    ·
      refine ⟨39380865281964044851881149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253910187976029901254099 39380865281964044851881149)
      ·
        refine ⟨14767824480736516819455431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39380865281964044851881149 14767824480736516819455431)
        ·
          refine ⟨22151736721104775229183147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767824480736516819455431 22151736721104775229183147)
          ·
            refine ⟨33227605081657162843774721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22151736721104775229183147 33227605081657162843774721)
            ·
              refine ⟨24920703811242872132831041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33227605081657162843774721 24920703811242872132831041)
              ·
                refine ⟨18690527858432154099623281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920703811242872132831041 18690527858432154099623281)
                ·
                  refine ⟨14017895893824115574717461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18690527858432154099623281 14017895893824115574717461)
                  ·
                    refine ⟨657088870023005417564881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14017895893824115574717461 657088870023005417564881)
                    ·
                      rfl

theorem cell22_1919514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1919514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919514 prefixEnd_1919514 := by exact prefixLift 1919514
  have htrace : WordTrace (prefixWord ++ tailWord_1919514) baseStart_1919514 baseEnd_1919514 := by
    simpa [prefixWord, tailWord_1919514, baseEnd_1919514] using wordTrace_append hprefix tailTrace_1919514
  have hstable : (prefixWord ++ tailWord_1919514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919514).length < 2 ^ (prefixWord ++ tailWord_1919514).sum := by decide
  have hdescent : baseEnd_1919514 < baseStart_1919514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919556 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1919556 : Nat := 118140960795 + 1919556 * 2 ^ 59
def prefixEnd_1919556 : Nat := 4983230072969 + 3 ^ 40 * 1919556 * 2
def baseEnd_1919556 : Nat := 657103247481331308014753

theorem tailTrace_1919556 : CollatzResearch.WordTrace tailWord_1919556 prefixEnd_1919556 657103247481331308014753 := by
  unfold tailWord_1919556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35005979516891960454853261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46674639355855947273137681 35005979516891960454853261)
  ·
    refine ⟨13127242318834485170569973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35005979516891960454853261 13127242318834485170569973)
    ·
      refine ⟨1230678967390732984740935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13127242318834485170569973 1230678967390732984740935)
      ·
        refine ⟨1846018451086099477111403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230678967390732984740935 1846018451086099477111403)
        ·
          refine ⟨2769027676629149215667105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846018451086099477111403 2769027676629149215667105)
          ·
            refine ⟨2076770757471861911750329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769027676629149215667105 2076770757471861911750329)
            ·
              refine ⟨1557578068103896433812747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076770757471861911750329 1557578068103896433812747)
              ·
                refine ⟨2336367102155844650719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557578068103896433812747 2336367102155844650719121)
                ·
                  refine ⟨1752275326616883488039341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336367102155844650719121 1752275326616883488039341)
                  ·
                    refine ⟨657103247481331308014753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752275326616883488039341 657103247481331308014753)
                    ·
                      rfl

theorem cell22_1919556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1919556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919556 prefixEnd_1919556 := by exact prefixLift 1919556
  have htrace : WordTrace (prefixWord ++ tailWord_1919556) baseStart_1919556 baseEnd_1919556 := by
    simpa [prefixWord, tailWord_1919556, baseEnd_1919556] using wordTrace_append hprefix tailTrace_1919556
  have hstable : (prefixWord ++ tailWord_1919556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919556).length < 2 ^ (prefixWord ++ tailWord_1919556).sum := by decide
  have hdescent : baseEnd_1919556 < baseStart_1919556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919623 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1919623 : Nat := 118140960795 + 1919623 * 2 ^ 59
def prefixEnd_1919623 : Nat := 4983230072969 + 3 ^ 40 * 1919623 * 2
def baseEnd_1919623 : Nat := 657126182950565466589547

theorem tailTrace_1919623 : CollatzResearch.WordTrace tailWord_1919623 prefixEnd_1919623 657126182950565466589547 := by
  unfold tailWord_1919623
  simp only [CollatzResearch.WordTrace]
  refine ⟨70014402724541191352395523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46676268483027460901597015 70014402724541191352395523)
  ·
    refine ⟨105021604086811787028593285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70014402724541191352395523 105021604086811787028593285)
    ·
      refine ⟨19691550766277210067861241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105021604086811787028593285 19691550766277210067861241)
      ·
        refine ⟨14768663074707907550895931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19691550766277210067861241 14768663074707907550895931)
        ·
          refine ⟨22152994612061861326343897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14768663074707907550895931 22152994612061861326343897)
          ·
            refine ⟨16614745959046395994757923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22152994612061861326343897 16614745959046395994757923)
            ·
              refine ⟨24922118938569593992136885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614745959046395994757923 24922118938569593992136885)
              ·
                refine ⟨2336448650490899436762833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24922118938569593992136885 2336448650490899436762833)
                ·
                  refine ⟨1752336487868174577572125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336448650490899436762833 1752336487868174577572125)
                  ·
                    refine ⟨657126182950565466589547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752336487868174577572125 657126182950565466589547)
                    ·
                      rfl

theorem cell22_1919623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1919623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919623 prefixEnd_1919623 := by exact prefixLift 1919623
  have htrace : WordTrace (prefixWord ++ tailWord_1919623) baseStart_1919623 baseEnd_1919623 := by
    simpa [prefixWord, tailWord_1919623, baseEnd_1919623] using wordTrace_append hprefix tailTrace_1919623
  have hstable : (prefixWord ++ tailWord_1919623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919623).length < 2 ^ (prefixWord ++ tailWord_1919623).sum := by decide
  have hdescent : baseEnd_1919623 < baseStart_1919623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919642 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1919642 : Nat := 118140960795 + 1919642 * 2 ^ 59
def prefixEnd_1919642 : Nat := 4983230072969 + 3 ^ 40 * 1919642 * 2
def baseEnd_1919642 : Nat := 219044229012951916788163

theorem tailTrace_1919642 : CollatzResearch.WordTrace tailWord_1919642 prefixEnd_1919642 219044229012951916788163 := by
  unfold tailWord_1919642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503773927868089399334295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46676730474314905064891453 17503773927868089399334295)
  ·
    refine ⟨26255660891802134099001443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503773927868089399334295 26255660891802134099001443)
    ·
      refine ⟨39383491337703201148502165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26255660891802134099001443 39383491337703201148502165)
      ·
        refine ⟨1846101156454837553836039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39383491337703201148502165 1846101156454837553836039)
        ·
          refine ⟨2769151734682256330754059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846101156454837553836039 2769151734682256330754059)
          ·
            refine ⟨4153727602023384496131089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769151734682256330754059 4153727602023384496131089)
            ·
              refine ⟨3115295701517538372098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153727602023384496131089 3115295701517538372098317)
              ·
                refine ⟨1168235888069076889536869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3115295701517538372098317 1168235888069076889536869)
                ·
                  refine ⟨219044229012951916788163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168235888069076889536869 219044229012951916788163)
                  ·
                    rfl

theorem cell22_1919642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1919642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919642 prefixEnd_1919642 := by exact prefixLift 1919642
  have htrace : WordTrace (prefixWord ++ tailWord_1919642) baseStart_1919642 baseEnd_1919642 := by
    simpa [prefixWord, tailWord_1919642, baseEnd_1919642] using wordTrace_append hprefix tailTrace_1919642
  have hstable : (prefixWord ++ tailWord_1919642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919642).length < 2 ^ (prefixWord ++ tailWord_1919642).sum := by decide
  have hdescent : baseEnd_1919642 < baseStart_1919642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919775 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 2, 3]
def baseStart_1919775 : Nat := 118140960795 + 1919775 * 2 ^ 59
def prefixEnd_1919775 : Nat := 4983230072969 + 3 ^ 40 * 1919775 * 2
def baseEnd_1919775 : Nat := 657178215656887736789081

theorem tailTrace_1919775 : CollatzResearch.WordTrace tailWord_1919775 prefixEnd_1919775 657178215656887736789081 := by
  unfold tailWord_1919775
  simp only [CollatzResearch.WordTrace]
  refine ⟨70019946619990521311928779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46679964413327014207952519 70019946619990521311928779)
  ·
    refine ⟨105029919929985781967893169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70019946619990521311928779 105029919929985781967893169)
    ·
      refine ⟨78772439947489336475919877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105029919929985781967893169 78772439947489336475919877)
      ·
        refine ⟨14769832490154250589234977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78772439947489336475919877 14769832490154250589234977)
        ·
          refine ⟨11077374367615687941926233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14769832490154250589234977 11077374367615687941926233)
          ·
            refine ⟨8308030775711765956444675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11077374367615687941926233 8308030775711765956444675)
            ·
              refine ⟨12462046163567648934667013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308030775711765956444675 12462046163567648934667013)
              ·
                refine ⟨2336633655668934175250065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12462046163567648934667013 2336633655668934175250065)
                ·
                  refine ⟨1752475241751700631437549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336633655668934175250065 1752475241751700631437549)
                  ·
                    refine ⟨657178215656887736789081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752475241751700631437549 657178215656887736789081)
                    ·
                      rfl

theorem cell22_1919775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_1919775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919775 prefixEnd_1919775 := by exact prefixLift 1919775
  have htrace : WordTrace (prefixWord ++ tailWord_1919775) baseStart_1919775 baseEnd_1919775 := by
    simpa [prefixWord, tailWord_1919775, baseEnd_1919775] using wordTrace_append hprefix tailTrace_1919775
  have hstable : (prefixWord ++ tailWord_1919775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919775).length < 2 ^ (prefixWord ++ tailWord_1919775).sum := by decide
  have hdescent : baseEnd_1919775 < baseStart_1919775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919833 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 7]
def baseStart_1919833 : Nat := 118140960795 + 1919833 * 2 ^ 59
def prefixEnd_1919833 : Nat := 4983230072969 + 3 ^ 40 * 1919833 * 2
def baseEnd_1919833 : Nat := 219066023414064972946301

theorem tailTrace_1919833 : CollatzResearch.WordTrace tailWord_1919833 prefixEnd_1919833 219066023414064972946301 := by
  unfold tailWord_1919833
  simp only [CollatzResearch.WordTrace]
  refine ⟨70022062053780397217540153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46681374702520264811693435 70022062053780397217540153)
  ·
    refine ⟨52516546540335297913155115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70022062053780397217540153 52516546540335297913155115)
    ·
      refine ⟨78774819810502946869732673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52516546540335297913155115 78774819810502946869732673)
      ·
        refine ⟨59081114857877210152299505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78774819810502946869732673 59081114857877210152299505)
        ·
          refine ⟨44310836143407907614224629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59081114857877210152299505 44310836143407907614224629)
          ·
            refine ⟨4154140888444491338833559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44310836143407907614224629 4154140888444491338833559)
            ·
              refine ⟨6231211332666737008250339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154140888444491338833559 6231211332666737008250339)
              ·
                refine ⟨9346816999000105512375509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231211332666737008250339 9346816999000105512375509)
                ·
                  refine ⟨219066023414064972946301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9346816999000105512375509 219066023414064972946301)
                  ·
                    rfl

theorem cell22_1919833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_1919833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919833 prefixEnd_1919833 := by exact prefixLift 1919833
  have htrace : WordTrace (prefixWord ++ tailWord_1919833) baseStart_1919833 baseEnd_1919833 := by
    simpa [prefixWord, tailWord_1919833, baseEnd_1919833] using wordTrace_append hprefix tailTrace_1919833
  have hstable : (prefixWord ++ tailWord_1919833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919833).length < 2 ^ (prefixWord ++ tailWord_1919833).sum := by decide
  have hdescent : baseEnd_1919833 < baseStart_1919833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919863 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1919863 : Nat := 118140960795 + 1919863 * 2 ^ 59
def prefixEnd_1919863 : Nat := 4983230072969 + 3 ^ 40 * 1919863 * 2
def baseEnd_1919863 : Nat := 657208339855284840588811

theorem tailTrace_1919863 : CollatzResearch.WordTrace tailWord_1919863 prefixEnd_1919863 657208339855284840588811 := by
  unfold tailWord_1919863
  simp only [CollatzResearch.WordTrace]
  refine ⟨70023156243671712341132243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46682104162447808227421495 70023156243671712341132243)
  ·
    refine ⟨105034734365507568511698365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70023156243671712341132243 105034734365507568511698365)
    ·
      refine ⟨39388025387065338191886887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105034734365507568511698365 39388025387065338191886887)
      ·
        refine ⟨59082038080598007287830331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39388025387065338191886887 59082038080598007287830331)
        ·
          refine ⟨88623057120897010931745497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59082038080598007287830331 88623057120897010931745497)
          ·
            refine ⟨66467292840672758198809123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88623057120897010931745497 66467292840672758198809123)
            ·
              refine ⟨99700939261009137298213685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66467292840672758198809123 99700939261009137298213685)
              ·
                refine ⟨9346963055719606621707533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99700939261009137298213685 9346963055719606621707533)
                ·
                  refine ⟨3505111145894852483140325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9346963055719606621707533 3505111145894852483140325)
                  ·
                    refine ⟨657208339855284840588811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3505111145894852483140325 657208339855284840588811)
                    ·
                      rfl

theorem cell22_1919863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1919863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919863 prefixEnd_1919863 := by exact prefixLift 1919863
  have htrace : WordTrace (prefixWord ++ tailWord_1919863) baseStart_1919863 baseEnd_1919863 := by
    simpa [prefixWord, tailWord_1919863, baseEnd_1919863] using wordTrace_append hprefix tailTrace_1919863
  have hstable : (prefixWord ++ tailWord_1919863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919863).length < 2 ^ (prefixWord ++ tailWord_1919863).sum := by decide
  have hdescent : baseEnd_1919863 < baseStart_1919863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919940 : List Nat := [2, 3, 3, 3, 11]
def baseStart_1919940 : Nat := 118140960795 + 1919940 * 2 ^ 59
def prefixEnd_1919940 : Nat := 4983230072969 + 3 ^ 40 * 1919940 * 2
def baseEnd_1919940 : Nat := 2704669541271120602525

theorem tailTrace_1919940 : CollatzResearch.WordTrace tailWord_1919940 prefixEnd_1919940 2704669541271120602525 := by
  unfold tailWord_1919940
  simp only [CollatzResearch.WordTrace]
  refine ⟨35012982332196377245842637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46683976442928502994456849 35012982332196377245842637)
  ·
    refine ⟨13129868374573641467190989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35012982332196377245842637 13129868374573641467190989)
    ·
      refine ⟨4923700640465115550196621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13129868374573641467190989 4923700640465115550196621)
      ·
        refine ⟨1846387740174418331323733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4923700640465115550196621 1846387740174418331323733)
        ·
          refine ⟨2704669541271120602525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1846387740174418331323733 2704669541271120602525)
          ·
            rfl

theorem cell22_1919940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 11].length) (baseStart_1919940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919940 prefixEnd_1919940 := by exact prefixLift 1919940
  have htrace : WordTrace (prefixWord ++ tailWord_1919940) baseStart_1919940 baseEnd_1919940 := by
    simpa [prefixWord, tailWord_1919940, baseEnd_1919940] using wordTrace_append hprefix tailTrace_1919940
  have hstable : (prefixWord ++ tailWord_1919940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919940).length < 2 ^ (prefixWord ++ tailWord_1919940).sum := by decide
  have hdescent : baseEnd_1919940 < baseStart_1919940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919944 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_1919944 : Nat := 118140960795 + 1919944 * 2 ^ 59
def prefixEnd_1919944 : Nat := 4983230072969 + 3 ^ 40 * 1919944 * 2
def baseEnd_1919944 : Nat := 657236067810627629313563

theorem tailTrace_1919944 : CollatzResearch.WordTrace tailWord_1919944 prefixEnd_1919944 657236067810627629313563 := by
  unfold tailWord_1919944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35013055278189131587415443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46684073704252175449887257 35013055278189131587415443)
  ·
    refine ⟨52519582917283697381123165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35013055278189131587415443 52519582917283697381123165)
    ·
      refine ⟨19694843593981386517921187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52519582917283697381123165 19694843593981386517921187)
      ·
        refine ⟨29542265390972079776881781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694843593981386517921187 29542265390972079776881781)
        ·
          refine ⟨2769587380403632479082667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29542265390972079776881781 2769587380403632479082667)
          ·
            refine ⟨4154381070605448718624001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769587380403632479082667 4154381070605448718624001)
            ·
              refine ⟨3115785802954086538968001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154381070605448718624001 3115785802954086538968001)
              ·
                refine ⟨2336839352215564904226001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115785802954086538968001 2336839352215564904226001)
                ·
                  refine ⟨1752629514161673678169501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336839352215564904226001 1752629514161673678169501)
                  ·
                    refine ⟨657236067810627629313563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752629514161673678169501 657236067810627629313563)
                    ·
                      rfl

theorem cell22_1919944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_1919944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919944 prefixEnd_1919944 := by exact prefixLift 1919944
  have htrace : WordTrace (prefixWord ++ tailWord_1919944) baseStart_1919944 baseEnd_1919944 := by
    simpa [prefixWord, tailWord_1919944, baseEnd_1919944] using wordTrace_append hprefix tailTrace_1919944
  have hstable : (prefixWord ++ tailWord_1919944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919944).length < 2 ^ (prefixWord ++ tailWord_1919944).sum := by decide
  have hdescent : baseEnd_1919944 < baseStart_1919944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919953 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1919953 : Nat := 118140960795 + 1919953 * 2 ^ 59
def prefixEnd_1919953 : Nat := 4983230072969 + 3 ^ 40 * 1919953 * 2
def baseEnd_1919953 : Nat := 657239148694554605838535

theorem tailTrace_1919953 : CollatzResearch.WordTrace tailWord_1919953 prefixEnd_1919953 657239148694554605838535 := by
  unfold tailWord_1919953
  simp only [CollatzResearch.WordTrace]
  refine ⟨70026438813345657711908513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46684292542230438474605675 70026438813345657711908513)
  ·
    refine ⟨52519829110009243283931385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70026438813345657711908513 52519829110009243283931385)
    ·
      refine ⟨39389871832506932462948539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52519829110009243283931385 39389871832506932462948539)
      ·
        refine ⟨59084807748760398694422809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39389871832506932462948539 59084807748760398694422809)
        ·
          refine ⟨44313605811570299020817107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59084807748760398694422809 44313605811570299020817107)
          ·
            refine ⟨66470408717355448531225661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44313605811570299020817107 66470408717355448531225661)
            ·
              refine ⟨24926403269008293199209623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66470408717355448531225661 24926403269008293199209623)
              ·
                refine ⟨37389604903512439798814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24926403269008293199209623 37389604903512439798814435)
                ·
                  refine ⟨56084407355268659698221653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37389604903512439798814435 56084407355268659698221653)
                  ·
                    refine ⟨657239148694554605838535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56084407355268659698221653 657239148694554605838535)
                    ·
                      rfl

theorem cell22_1919953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1919953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919953 prefixEnd_1919953 := by exact prefixLift 1919953
  have htrace : WordTrace (prefixWord ++ tailWord_1919953) baseStart_1919953 baseEnd_1919953 := by
    simpa [prefixWord, tailWord_1919953, baseEnd_1919953] using wordTrace_append hprefix tailTrace_1919953
  have hstable : (prefixWord ++ tailWord_1919953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919953).length < 2 ^ (prefixWord ++ tailWord_1919953).sum := by decide
  have hdescent : baseEnd_1919953 < baseStart_1919953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919957 : List Nat := [1, 3, 2, 3, 3, 2, 1, 7]
def baseStart_1919957 : Nat := 118140960795 + 1919957 * 2 ^ 59
def prefixEnd_1919957 : Nat := 4983230072969 + 3 ^ 40 * 1919957 * 2
def baseEnd_1919957 : Nat := 73026724219588880970947

theorem tailTrace_1919957 : CollatzResearch.WordTrace tailWord_1919957 prefixEnd_1919957 73026724219588880970947 := by
  unfold tailWord_1919957
  simp only [CollatzResearch.WordTrace]
  refine ⟨70026584705331166395054125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46684389803554110930036083 70026584705331166395054125)
  ·
    refine ⟨26259969264499187398145297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70026584705331166395054125 26259969264499187398145297)
    ·
      refine ⟨19694976948374390548608973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26259969264499187398145297 19694976948374390548608973)
      ·
        refine ⟨7385616355640396455728365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19694976948374390548608973 7385616355640396455728365)
        ·
          refine ⟨2769606133365148670898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7385616355640396455728365 2769606133365148670898137)
          ·
            refine ⟨2077204600023861503173603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769606133365148670898137 2077204600023861503173603)
            ·
              refine ⟨3115806900035792254760405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077204600023861503173603 3115806900035792254760405)
              ·
                refine ⟨73026724219588880970947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3115806900035792254760405 73026724219588880970947)
                ·
                  rfl

theorem cell22_1919957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 7].length) (baseStart_1919957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919957 prefixEnd_1919957 := by exact prefixLift 1919957
  have htrace : WordTrace (prefixWord ++ tailWord_1919957) baseStart_1919957 baseEnd_1919957 := by
    simpa [prefixWord, tailWord_1919957, baseEnd_1919957] using wordTrace_append hprefix tailTrace_1919957
  have hstable : (prefixWord ++ tailWord_1919957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919957).length < 2 ^ (prefixWord ++ tailWord_1919957).sum := by decide
  have hdescent : baseEnd_1919957 < baseStart_1919957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919968 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_1919968 : Nat := 118140960795 + 1919968 * 2 ^ 59
def prefixEnd_1919968 : Nat := 4983230072969 + 3 ^ 40 * 1919968 * 2
def baseEnd_1919968 : Nat := 219081427833699855571163

theorem tailTrace_1919968 : CollatzResearch.WordTrace tailWord_1919968 prefixEnd_1919968 219081427833699855571163 := by
  unfold tailWord_1919968
  simp only [CollatzResearch.WordTrace]
  refine ⟨35013492954145657636852279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46684657272194210182469705 35013492954145657636852279)
  ·
    refine ⟨52520239431218486455278419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35013492954145657636852279 52520239431218486455278419)
    ·
      refine ⟨78780359146827729682917629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52520239431218486455278419 78780359146827729682917629)
      ·
        refine ⟨29542634680060398631094111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78780359146827729682917629 29542634680060398631094111)
        ·
          refine ⟨44313952020090597946641167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29542634680060398631094111 44313952020090597946641167)
          ·
            refine ⟨66470928030135896919961751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44313952020090597946641167 66470928030135896919961751)
            ·
              refine ⟨99706392045203845379942627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66470928030135896919961751 99706392045203845379942627)
              ·
                refine ⟨149559588067805768069913941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99706392045203845379942627 149559588067805768069913941)
                ·
                  refine ⟨219081427833699855571163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 149559588067805768069913941 219081427833699855571163)
                  ·
                    rfl

theorem cell22_1919968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_1919968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1919968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1919968 prefixEnd_1919968 := by exact prefixLift 1919968
  have htrace : WordTrace (prefixWord ++ tailWord_1919968) baseStart_1919968 baseEnd_1919968 := by
    simpa [prefixWord, tailWord_1919968, baseEnd_1919968] using wordTrace_append hprefix tailTrace_1919968
  have hstable : (prefixWord ++ tailWord_1919968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919968).length < 2 ^ (prefixWord ++ tailWord_1919968).sum := by decide
  have hdescent : baseEnd_1919968 < baseStart_1919968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920064 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_1920064 : Nat := 118140960795 + 1920064 * 2 ^ 59
def prefixEnd_1920064 : Nat := 4983230072969 + 3 ^ 40 * 1920064 * 2
def baseEnd_1920064 : Nat := 219092382087662438771065

theorem tailTrace_1920064 : CollatzResearch.WordTrace tailWord_1920064 prefixEnd_1920064 219092382087662438771065 := by
  unfold tailWord_1920064
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015243657971761834599623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46686991543962349112799497 35015243657971761834599623)
  ·
    refine ⟨52522865486957642751899435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35015243657971761834599623 52522865486957642751899435)
    ·
      refine ⟨78784298230436464127849153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52522865486957642751899435 78784298230436464127849153)
      ·
        refine ⟨59088223672827348095886865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78784298230436464127849153 59088223672827348095886865)
        ·
          refine ⟨44316167754620511071915149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59088223672827348095886865 44316167754620511071915149)
          ·
            refine ⟨16618562907982691651968181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44316167754620511071915149 16618562907982691651968181)
            ·
              refine ⟨1557990272623377342372017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16618562907982691651968181 1557990272623377342372017)
              ·
                refine ⟨1168492704467533006779013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557990272623377342372017 1168492704467533006779013)
                ·
                  refine ⟨219092382087662438771065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168492704467533006779013 219092382087662438771065)
                  ·
                    rfl

theorem cell22_1920064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_1920064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920064 prefixEnd_1920064 := by exact prefixLift 1920064
  have htrace : WordTrace (prefixWord ++ tailWord_1920064) baseStart_1920064 baseEnd_1920064 := by
    simpa [prefixWord, tailWord_1920064, baseEnd_1920064] using wordTrace_append hprefix tailTrace_1920064
  have hstable : (prefixWord ++ tailWord_1920064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920064).length < 2 ^ (prefixWord ++ tailWord_1920064).sum := by decide
  have hdescent : baseEnd_1920064 < baseStart_1920064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920120 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_1920120 : Nat := 118140960795 + 1920120 * 2 ^ 59
def prefixEnd_1920120 : Nat := 4983230072969 + 3 ^ 40 * 1920120 * 2
def baseEnd_1920120 : Nat := 219098772069140612304341

theorem tailTrace_1920120 : CollatzResearch.WordTrace tailWord_1920120 prefixEnd_1920120 219098772069140612304341 := by
  unfold tailWord_1920120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35016264901870322616618907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46688353202493763488825209 35016264901870322616618907)
  ·
    refine ⟨52524397352805483924928361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35016264901870322616618907 52524397352805483924928361)
    ·
      refine ⟨39393298014604112943696271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52524397352805483924928361 39393298014604112943696271)
      ·
        refine ⟨59089947021906169415544407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39393298014604112943696271 59089947021906169415544407)
        ·
          refine ⟨88634920532859254123316611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59089947021906169415544407 88634920532859254123316611)
          ·
            refine ⟨132952380799288881184974917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88634920532859254123316611 132952380799288881184974917)
            ·
              refine ⟨24928571399866665222182797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132952380799288881184974917 24928571399866665222182797)
              ·
                refine ⟨9348214274949999458318549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24928571399866665222182797 9348214274949999458318549)
                ·
                  refine ⟨219098772069140612304341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9348214274949999458318549 219098772069140612304341)
                  ·
                    rfl

theorem cell22_1920120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_1920120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920120 prefixEnd_1920120 := by exact prefixLift 1920120
  have htrace : WordTrace (prefixWord ++ tailWord_1920120) baseStart_1920120 baseEnd_1920120 := by
    simpa [prefixWord, tailWord_1920120, baseEnd_1920120] using wordTrace_append hprefix tailTrace_1920120
  have hstable : (prefixWord ++ tailWord_1920120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920120).length < 2 ^ (prefixWord ++ tailWord_1920120).sum := by decide
  have hdescent : baseEnd_1920120 < baseStart_1920120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920137 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 5]
def baseStart_1920137 : Nat := 118140960795 + 1920137 * 2 ^ 59
def prefixEnd_1920137 : Nat := 4983230072969 + 3 ^ 40 * 1920137 * 2
def baseEnd_1920137 : Nat := 219100711884946486412657

theorem tailTrace_1920137 : CollatzResearch.WordTrace tailWord_1920137 prefixEnd_1920137 219100711884946486412657 := by
  unfold tailWord_1920137
  simp only [CollatzResearch.WordTrace]
  refine ⟨70033149844679057136606665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46688766563119371424404443 70033149844679057136606665)
  ·
    refine ⟨52524862383509292852454999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70033149844679057136606665 52524862383509292852454999)
    ·
      refine ⟨78787293575263939278682499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52524862383509292852454999 78787293575263939278682499)
      ·
        refine ⟨118180940362895908918023749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78787293575263939278682499 118180940362895908918023749)
        ·
          refine ⟨22158926318042982922129453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118180940362895908918023749 22158926318042982922129453)
          ·
            refine ⟨8309597369266118595798545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22158926318042982922129453 8309597369266118595798545)
            ·
              refine ⟨6232198026949588946848909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309597369266118595798545 6232198026949588946848909)
              ·
                refine ⟨2337074260106095855068341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6232198026949588946848909 2337074260106095855068341)
                ·
                  refine ⟨219100711884946486412657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2337074260106095855068341 219100711884946486412657)
                  ·
                    rfl

theorem cell22_1920137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_1920137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920137 prefixEnd_1920137 := by exact prefixLift 1920137
  have htrace : WordTrace (prefixWord ++ tailWord_1920137) baseStart_1920137 baseEnd_1920137 := by
    simpa [prefixWord, tailWord_1920137, baseEnd_1920137] using wordTrace_append hprefix tailTrace_1920137
  have hstable : (prefixWord ++ tailWord_1920137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920137).length < 2 ^ (prefixWord ++ tailWord_1920137).sum := by decide
  have hdescent : baseEnd_1920137 < baseStart_1920137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920158 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1920158 : Nat := 118140960795 + 1920158 * 2 ^ 59
def prefixEnd_1920158 : Nat := 4983230072969 + 3 ^ 40 * 1920158 * 2
def baseEnd_1920158 : Nat := 657309324384002404462907

theorem tailTrace_1920158 : CollatzResearch.WordTrace tailWord_1920158 prefixEnd_1920158 657309324384002404462907 := by
  unfold tailWord_1920158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754239472200372215390141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46689277185068651815414085 8754239472200372215390141)
  ·
    refine ⟨3282839802075139580771303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8754239472200372215390141 3282839802075139580771303)
    ·
      refine ⟨4924259703112709371156955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282839802075139580771303 4924259703112709371156955)
      ·
        refine ⟨7386389554669064056735433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924259703112709371156955 7386389554669064056735433)
        ·
          refine ⟨5539792166001798042551575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7386389554669064056735433 5539792166001798042551575)
          ·
            refine ⟨8309688249002697063827363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539792166001798042551575 8309688249002697063827363)
            ·
              refine ⟨12464532373504045595741045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309688249002697063827363 12464532373504045595741045)
              ·
                refine ⟨1168549910016004274600723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12464532373504045595741045 1168549910016004274600723)
                ·
                  refine ⟨1752824865024006411901085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168549910016004274600723 1752824865024006411901085)
                  ·
                    refine ⟨657309324384002404462907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752824865024006411901085 657309324384002404462907)
                    ·
                      rfl

theorem cell22_1920158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1920158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920158 prefixEnd_1920158 := by exact prefixLift 1920158
  have htrace : WordTrace (prefixWord ++ tailWord_1920158) baseStart_1920158 baseEnd_1920158 := by
    simpa [prefixWord, tailWord_1920158, baseEnd_1920158] using wordTrace_append hprefix tailTrace_1920158
  have hstable : (prefixWord ++ tailWord_1920158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920158).length < 2 ^ (prefixWord ++ tailWord_1920158).sum := by decide
  have hdescent : baseEnd_1920158 < baseStart_1920158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920293 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_1920293 : Nat := 118140960795 + 1920293 * 2 ^ 59
def prefixEnd_1920293 : Nat := 4983230072969 + 3 ^ 40 * 1920293 * 2
def baseEnd_1920293 : Nat := 657355537642907052337493

theorem tailTrace_1920293 : CollatzResearch.WordTrace tailWord_1920293 prefixEnd_1920293 657355537642907052337493 := by
  unfold tailWord_1920293
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038839632113895779285533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46692559754742597186190355 70038839632113895779285533)
  ·
    refine ⟨26264564862042710917232075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70038839632113895779285533 26264564862042710917232075)
    ·
      refine ⟨39396847293064066375848113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26264564862042710917232075 39396847293064066375848113)
      ·
        refine ⟨29547635469798049781886085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39396847293064066375848113 29547635469798049781886085)
        ·
          refine ⟨5540181650587134334103641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29547635469798049781886085 5540181650587134334103641)
          ·
            refine ⟨4155136237940350750577731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540181650587134334103641 4155136237940350750577731)
            ·
              refine ⟨6232704356910526125866597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155136237940350750577731 6232704356910526125866597)
              ·
                refine ⟨1168632066920723648599987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6232704356910526125866597 1168632066920723648599987)
                ·
                  refine ⟨1752948100381085472899981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168632066920723648599987 1752948100381085472899981)
                  ·
                    refine ⟨657355537642907052337493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752948100381085472899981 657355537642907052337493)
                    ·
                      rfl

theorem cell22_1920293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_1920293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920293 prefixEnd_1920293 := by exact prefixLift 1920293
  have htrace : WordTrace (prefixWord ++ tailWord_1920293) baseStart_1920293 baseEnd_1920293 := by
    simpa [prefixWord, tailWord_1920293, baseEnd_1920293] using wordTrace_append hprefix tailTrace_1920293
  have hstable : (prefixWord ++ tailWord_1920293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920293).length < 2 ^ (prefixWord ++ tailWord_1920293).sum := by decide
  have hdescent : baseEnd_1920293 < baseStart_1920293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920310 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1920310 : Nat := 118140960795 + 1920310 * 2 ^ 59
def prefixEnd_1920310 : Nat := 4983230072969 + 3 ^ 40 * 1920310 * 2
def baseEnd_1920310 : Nat := 657361357090324674662441

theorem tailTrace_1920310 : CollatzResearch.WordTrace tailWord_1920310 prefixEnd_1920310 657361357090324674662441 := by
  unfold tailWord_1920310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377466229565769230165899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46692973115368205121769589 4377466229565769230165899)
  ·
    refine ⟨6566199344348653845248849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377466229565769230165899 6566199344348653845248849)
    ·
      refine ⟨4924649508261490383936637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6566199344348653845248849 4924649508261490383936637)
      ·
        refine ⟨1846743565598058893976239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4924649508261490383936637 1846743565598058893976239)
        ·
          refine ⟨2770115348397088340964359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846743565598058893976239 2770115348397088340964359)
          ·
            refine ⟨4155173022595632511446539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770115348397088340964359 4155173022595632511446539)
            ·
              refine ⟨6232759533893448767169809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155173022595632511446539 6232759533893448767169809)
              ·
                refine ⟨4674569650420086575377357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232759533893448767169809 4674569650420086575377357)
                ·
                  refine ⟨1752963618907532465766509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4674569650420086575377357 1752963618907532465766509)
                  ·
                    refine ⟨657361357090324674662441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1752963618907532465766509 657361357090324674662441)
                    ·
                      rfl

theorem cell22_1920310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1920310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920310 prefixEnd_1920310 := by exact prefixLift 1920310
  have htrace : WordTrace (prefixWord ++ tailWord_1920310) baseStart_1920310 baseEnd_1920310 := by
    simpa [prefixWord, tailWord_1920310, baseEnd_1920310] using wordTrace_append hprefix tailTrace_1920310
  have hstable : (prefixWord ++ tailWord_1920310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920310).length < 2 ^ (prefixWord ++ tailWord_1920310).sum := by decide
  have hdescent : baseEnd_1920310 < baseStart_1920310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920319 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_1920319 : Nat := 118140960795 + 1920319 * 2 ^ 59
def prefixEnd_1920319 : Nat := 4983230072969 + 3 ^ 40 * 1920319 * 2
def baseEnd_1920319 : Nat := 657364437974251651187413

theorem tailTrace_1920319 : CollatzResearch.WordTrace tailWord_1920319 prefixEnd_1920319 657364437974251651187413 := by
  unfold tailWord_1920319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70039787930019702219732011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46693191953346468146488007 70039787930019702219732011)
  ·
    refine ⟨105059681895029553329598017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70039787930019702219732011 105059681895029553329598017)
    ·
      refine ⟨78794761421272164997198513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105059681895029553329598017 78794761421272164997198513)
      ·
        refine ⟨59096071065954123747898885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78794761421272164997198513 59096071065954123747898885)
        ·
          refine ⟨11080513324866398202731041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59096071065954123747898885 11080513324866398202731041)
          ·
            refine ⟨8310384993649798652048281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080513324866398202731041 8310384993649798652048281)
            ·
              refine ⟨6232788745237348989036211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8310384993649798652048281 6232788745237348989036211)
              ·
                refine ⟨9349183117856023483554317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232788745237348989036211 9349183117856023483554317)
                ·
                  refine ⟨3505943669196008806332869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9349183117856023483554317 3505943669196008806332869)
                  ·
                    refine ⟨657364437974251651187413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3505943669196008806332869 657364437974251651187413)
                    ·
                      rfl

theorem cell22_1920319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_1920319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920319 prefixEnd_1920319 := by exact prefixLift 1920319
  have htrace : WordTrace (prefixWord ++ tailWord_1920319) baseStart_1920319 baseEnd_1920319 := by
    simpa [prefixWord, tailWord_1920319, baseEnd_1920319] using wordTrace_append hprefix tailTrace_1920319
  have hstable : (prefixWord ++ tailWord_1920319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920319).length < 2 ^ (prefixWord ++ tailWord_1920319).sum := by decide
  have hdescent : baseEnd_1920319 < baseStart_1920319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920364 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_1920364 : Nat := 118140960795 + 1920364 * 2 ^ 59
def prefixEnd_1920364 : Nat := 4983230072969 + 3 ^ 40 * 1920364 * 2
def baseEnd_1920364 : Nat := 657379842393886533812275

theorem tailTrace_1920364 : CollatzResearch.WordTrace tailWord_1920364 prefixEnd_1920364 657379842393886533812275 := by
  unfold tailWord_1920364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35020714607428337452560073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46694286143237783270080097 35020714607428337452560073)
  ·
    refine ⟨26265535955571253089420055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35020714607428337452560073 26265535955571253089420055)
    ·
      refine ⟨39398303933356879634130083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265535955571253089420055 39398303933356879634130083)
      ·
        refine ⟨59097455900035319451195125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39398303933356879634130083 59097455900035319451195125)
        ·
          refine ⟨5540386490628311198549543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59097455900035319451195125 5540386490628311198549543)
          ·
            refine ⟨8310579735942466797824315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540386490628311198549543 8310579735942466797824315)
            ·
              refine ⟨12465869603913700196736473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310579735942466797824315 12465869603913700196736473)
              ·
                refine ⟨9349402202935275147552355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12465869603913700196736473 9349402202935275147552355)
                ·
                  refine ⟨14024103304402912721328533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9349402202935275147552355 14024103304402912721328533)
                  ·
                    refine ⟨657379842393886533812275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14024103304402912721328533 657379842393886533812275)
                    ·
                      rfl

theorem cell22_1920364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_1920364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920364 prefixEnd_1920364 := by exact prefixLift 1920364
  have htrace : WordTrace (prefixWord ++ tailWord_1920364) baseStart_1920364 baseEnd_1920364 := by
    simpa [prefixWord, tailWord_1920364, baseEnd_1920364] using wordTrace_append hprefix tailTrace_1920364
  have hstable : (prefixWord ++ tailWord_1920364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920364).length < 2 ^ (prefixWord ++ tailWord_1920364).sum := by decide
  have hdescent : baseEnd_1920364 < baseStart_1920364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920385 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 4]
def baseStart_1920385 : Nat := 118140960795 + 1920385 * 2 ^ 59
def prefixEnd_1920385 : Nat := 4983230072969 + 3 ^ 40 * 1920385 * 2
def baseEnd_1920385 : Nat := 219129010374349826345737

theorem tailTrace_1920385 : CollatzResearch.WordTrace tailWord_1920385 prefixEnd_1920385 219129010374349826345737 := by
  unfold tailWord_1920385
  simp only [CollatzResearch.WordTrace]
  refine ⟨70042195147780595491634609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46694796765187063661089739 70042195147780595491634609)
  ·
    refine ⟨52531646360835446618725957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70042195147780595491634609 52531646360835446618725957)
    ·
      refine ⟨9849683692656646241011117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52531646360835446618725957 9849683692656646241011117)
      ·
        refine ⟨3693631384746242340379169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9849683692656646241011117 3693631384746242340379169)
        ·
          refine ⟨2770223538559681755284377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693631384746242340379169 2770223538559681755284377)
          ·
            refine ⟨2077667653919761316463283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770223538559681755284377 2077667653919761316463283)
            ·
              refine ⟨3116501480879641974694925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077667653919761316463283 3116501480879641974694925)
              ·
                refine ⟨1168688055329865740510597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116501480879641974694925 1168688055329865740510597)
                ·
                  refine ⟨219129010374349826345737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168688055329865740510597 219129010374349826345737)
                  ·
                    rfl

theorem cell22_1920385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_1920385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920385 prefixEnd_1920385 := by exact prefixLift 1920385
  have htrace : WordTrace (prefixWord ++ tailWord_1920385) baseStart_1920385 baseEnd_1920385 := by
    simpa [prefixWord, tailWord_1920385, baseEnd_1920385] using wordTrace_append hprefix tailTrace_1920385
  have hstable : (prefixWord ++ tailWord_1920385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920385).length < 2 ^ (prefixWord ++ tailWord_1920385).sum := by decide
  have hdescent : baseEnd_1920385 < baseStart_1920385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920398 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1920398 : Nat := 118140960795 + 1920398 * 2 ^ 59
def prefixEnd_1920398 : Nat := 4983230072969 + 3 ^ 40 * 1920398 * 2
def baseEnd_1920398 : Nat := 657391481288721778462171

theorem tailTrace_1920398 : CollatzResearch.WordTrace tailWord_1920398 prefixEnd_1920398 657391481288721778462171 := by
  unfold tailWord_1920398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755333662091687338982231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46695112864488999141238565 8755333662091687338982231)
  ·
    refine ⟨13133000493137531008473347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755333662091687338982231 13133000493137531008473347)
    ·
      refine ⟨19699500739706296512710021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13133000493137531008473347 19699500739706296512710021)
      ·
        refine ⟨3693656388694930596133129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19699500739706296512710021 3693656388694930596133129)
        ·
          refine ⟨2770242291521197947099847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693656388694930596133129 2770242291521197947099847)
          ·
            refine ⟨4155363437281796920649771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770242291521197947099847 4155363437281796920649771)
            ·
              refine ⟨6233045155922695380974657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155363437281796920649771 6233045155922695380974657)
              ·
                refine ⟨4674783866942021535730993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233045155922695380974657 4674783866942021535730993)
                ·
                  refine ⟨3506087900206516151798245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674783866942021535730993 3506087900206516151798245)
                  ·
                    refine ⟨657391481288721778462171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3506087900206516151798245 657391481288721778462171)
                    ·
                      rfl

theorem cell22_1920398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1920398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920398 prefixEnd_1920398 := by exact prefixLift 1920398
  have htrace : WordTrace (prefixWord ++ tailWord_1920398) baseStart_1920398 baseEnd_1920398 := by
    simpa [prefixWord, tailWord_1920398, baseEnd_1920398] using wordTrace_append hprefix tailTrace_1920398
  have hstable : (prefixWord ++ tailWord_1920398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920398).length < 2 ^ (prefixWord ++ tailWord_1920398).sum := by decide
  have hdescent : baseEnd_1920398 < baseStart_1920398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920402 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1920402 : Nat := 118140960795 + 1920402 * 2 ^ 59
def prefixEnd_1920402 : Nat := 4983230072969 + 3 ^ 40 * 1920402 * 2
def baseEnd_1920402 : Nat := 219130950190155700454053

theorem tailTrace_1920402 : CollatzResearch.WordTrace tailWord_1920402 prefixEnd_1920402 219130950190155700454053 := by
  unfold tailWord_1920402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510703797179751848750865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46695210125812671596668973 17510703797179751848750865)
  ·
    refine ⟨13133027847884813886563149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17510703797179751848750865 13133027847884813886563149)
    ·
      refine ⟨4924885442956805207461181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13133027847884813886563149 4924885442956805207461181)
      ·
        refine ⟨1846832041108801952797943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4924885442956805207461181 1846832041108801952797943)
        ·
          refine ⟨2770248061663202929196915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846832041108801952797943 2770248061663202929196915)
          ·
            refine ⟨4155372092494804393795373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770248061663202929196915 4155372092494804393795373)
            ·
              refine ⟨1558264534685551647673265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4155372092494804393795373 1558264534685551647673265)
              ·
                refine ⟨1168698401014163735754949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558264534685551647673265 1168698401014163735754949)
                ·
                  refine ⟨219130950190155700454053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168698401014163735754949 219130950190155700454053)
                  ·
                    rfl

theorem cell22_1920402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1920402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920402 prefixEnd_1920402 := by exact prefixLift 1920402
  have htrace : WordTrace (prefixWord ++ tailWord_1920402) baseStart_1920402 baseEnd_1920402 := by
    simpa [prefixWord, tailWord_1920402, baseEnd_1920402] using wordTrace_append hprefix tailTrace_1920402
  have hstable : (prefixWord ++ tailWord_1920402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920402).length < 2 ^ (prefixWord ++ tailWord_1920402).sum := by decide
  have hdescent : baseEnd_1920402 < baseStart_1920402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920576 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_1920576 : Nat := 118140960795 + 1920576 * 2 ^ 59
def prefixEnd_1920576 : Nat := 4983230072969 + 3 ^ 40 * 1920576 * 2
def baseEnd_1920576 : Nat := 219150804775462882503875

theorem tailTrace_1920576 : CollatzResearch.WordTrace tailWord_1920576 prefixEnd_1920576 219150804775462882503875 := by
  unfold tailWord_1920576
  simp only [CollatzResearch.WordTrace]
  refine ⟨35024580745044317555918791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46699440993392423407891721 35024580745044317555918791)
  ·
    refine ⟨52536871117566476333878187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35024580745044317555918791 52536871117566476333878187)
    ·
      refine ⟨78805306676349714500817281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52536871117566476333878187 78805306676349714500817281)
      ·
        refine ⟨59103980007262285875612961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78805306676349714500817281 59103980007262285875612961)
        ·
          refine ⟨44327985005446714406709721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59103980007262285875612961 44327985005446714406709721)
          ·
            refine ⟨33245988754085035805032291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44327985005446714406709721 33245988754085035805032291)
            ·
              refine ⟨49868983131127553707548437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33245988754085035805032291 49868983131127553707548437)
              ·
                refine ⟨2337608584271604080041333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49868983131127553707548437 2337608584271604080041333)
                ·
                  refine ⟨219150804775462882503875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2337608584271604080041333 219150804775462882503875)
                  ·
                    rfl

theorem cell22_1920576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_1920576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920576 prefixEnd_1920576 := by exact prefixLift 1920576
  have htrace : WordTrace (prefixWord ++ tailWord_1920576) baseStart_1920576 baseEnd_1920576 := by
    simpa [prefixWord, tailWord_1920576, baseEnd_1920576] using wordTrace_append hprefix tailTrace_1920576
  have hstable : (prefixWord ++ tailWord_1920576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920576).length < 2 ^ (prefixWord ++ tailWord_1920576).sum := by decide
  have hdescent : baseEnd_1920576 < baseStart_1920576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920636 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1920636 : Nat := 118140960795 + 1920636 * 2 ^ 59
def prefixEnd_1920636 : Nat := 4983230072969 + 3 ^ 40 * 1920636 * 2
def baseEnd_1920636 : Nat := 657472953552568491011441

theorem tailTrace_1920636 : CollatzResearch.WordTrace tailWord_1920636 prefixEnd_1920636 657472953552568491011441 := by
  unfold tailWord_1920636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025674934935632679510881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46700899913247510239347841 35025674934935632679510881)
  ·
    refine ⟨26269256201201724509633161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35025674934935632679510881 26269256201201724509633161)
    ·
      refine ⟨19701942150901293382224871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26269256201201724509633161 19701942150901293382224871)
      ·
        refine ⟨29552913226351940073337307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701942150901293382224871 29552913226351940073337307)
        ·
          refine ⟨44329369839527910110005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29552913226351940073337307 44329369839527910110005961)
          ·
            refine ⟨33247027379645932582504471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44329369839527910110005961 33247027379645932582504471)
            ·
              refine ⟨49870541069468898873756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33247027379645932582504471 49870541069468898873756707)
              ·
                refine ⟨74805811604203348310635061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49870541069468898873756707 74805811604203348310635061)
                ·
                  refine ⟨7013044837894063904122037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74805811604203348310635061 7013044837894063904122037)
                  ·
                    refine ⟨657472953552568491011441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7013044837894063904122037 657472953552568491011441)
                    ·
                      rfl

theorem cell22_1920636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1920636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920636 prefixEnd_1920636 := by exact prefixLift 1920636
  have htrace : WordTrace (prefixWord ++ tailWord_1920636) baseStart_1920636 baseEnd_1920636 := by
    simpa [prefixWord, tailWord_1920636, baseEnd_1920636] using wordTrace_append hprefix tailTrace_1920636
  have hstable : (prefixWord ++ tailWord_1920636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920636).length < 2 ^ (prefixWord ++ tailWord_1920636).sum := by decide
  have hdescent : baseEnd_1920636 < baseStart_1920636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920651 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_1920651 : Nat := 118140960795 + 1920651 * 2 ^ 59
def prefixEnd_1920651 : Nat := 4983230072969 + 3 ^ 40 * 1920651 * 2
def baseEnd_1920651 : Nat := 657478088359113451886395

theorem tailTrace_1920651 : CollatzResearch.WordTrace tailWord_1920651 prefixEnd_1920651 657478088359113451886395 := by
  unfold tailWord_1920651
  simp only [CollatzResearch.WordTrace]
  refine ⟨70051896964816922920817807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46701264643211281947211871 70051896964816922920817807)
  ·
    refine ⟨105077845447225384381226711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70051896964816922920817807 105077845447225384381226711)
    ·
      refine ⟨157616768170838076571840067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105077845447225384381226711 157616768170838076571840067)
      ·
        refine ⟨236425152256257114857760101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157616768170838076571840067 236425152256257114857760101)
        ·
          refine ⟨44329716048048209035830019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236425152256257114857760101 44329716048048209035830019)
          ·
            refine ⟨66494574072072313553745029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44329716048048209035830019 66494574072072313553745029)
            ·
              refine ⟨12467732638513558791327193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66494574072072313553745029 12467732638513558791327193)
              ·
                refine ⟨9350799478885169093495395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12467732638513558791327193 9350799478885169093495395)
                ·
                  refine ⟨14026199218327753640243093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350799478885169093495395 14026199218327753640243093)
                  ·
                    refine ⟨657478088359113451886395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14026199218327753640243093 657478088359113451886395)
                    ·
                      rfl

theorem cell22_1920651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_1920651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920651 prefixEnd_1920651 := by exact prefixLift 1920651
  have htrace : WordTrace (prefixWord ++ tailWord_1920651) baseStart_1920651 baseEnd_1920651 := by
    simpa [prefixWord, tailWord_1920651, baseEnd_1920651] using wordTrace_append hprefix tailTrace_1920651
  have hstable : (prefixWord ++ tailWord_1920651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920651).length < 2 ^ (prefixWord ++ tailWord_1920651).sum := by decide
  have hdescent : baseEnd_1920651 < baseStart_1920651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920670 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1920670 : Nat := 118140960795 + 1920670 * 2 ^ 59
def prefixEnd_1920670 : Nat := 4983230072969 + 3 ^ 40 * 1920670 * 2
def baseEnd_1920670 : Nat := 657484592447403735661337

theorem tailTrace_1920670 : CollatzResearch.WordTrace tailWord_1920670 prefixEnd_1920670 657484592447403735661337 := by
  unfold tailWord_1920670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756573743968511145719933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46701726634498726110506309 8756573743968511145719933)
  ·
    refine ⟨3283715153988191679644975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8756573743968511145719933 3283715153988191679644975)
    ·
      refine ⟨4925572730982287519467463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3283715153988191679644975 4925572730982287519467463)
      ·
        refine ⟨7388359096473431279201195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925572730982287519467463 7388359096473431279201195)
        ·
          refine ⟨11082538644710146918801793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388359096473431279201195 11082538644710146918801793)
          ·
            refine ⟨8311903983532610189101345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11082538644710146918801793 8311903983532610189101345)
            ·
              refine ⟨6233927987649457641826009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8311903983532610189101345 6233927987649457641826009)
              ·
                refine ⟨4675445990737093231369507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6233927987649457641826009 4675445990737093231369507)
                ·
                  refine ⟨7013168986105639847054261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675445990737093231369507 7013168986105639847054261)
                  ·
                    refine ⟨657484592447403735661337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7013168986105639847054261 657484592447403735661337)
                    ·
                      rfl

theorem cell22_1920670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1920670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920670 prefixEnd_1920670 := by exact prefixLift 1920670
  have htrace : WordTrace (prefixWord ++ tailWord_1920670) baseStart_1920670 baseEnd_1920670 := by
    simpa [prefixWord, tailWord_1920670, baseEnd_1920670] using wordTrace_append hprefix tailTrace_1920670
  have hstable : (prefixWord ++ tailWord_1920670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920670).length < 2 ^ (prefixWord ++ tailWord_1920670).sum := by decide
  have hdescent : baseEnd_1920670 < baseStart_1920670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920696 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_1920696 : Nat := 118140960795 + 1920696 * 2 ^ 59
def prefixEnd_1920696 : Nat := 4983230072969 + 3 ^ 40 * 1920696 * 2
def baseEnd_1920696 : Nat := 657493492778748334511257

theorem tailTrace_1920696 : CollatzResearch.WordTrace tailWord_1920696 prefixEnd_1920696 657493492778748334511257 := by
  unfold tailWord_1920696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35026769124826947803102971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46702358833102597070803961 35026769124826947803102971)
  ·
    refine ⟨52540153687240421704654457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35026769124826947803102971 52540153687240421704654457)
    ·
      refine ⟨39405115265430316278490843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52540153687240421704654457 39405115265430316278490843)
      ·
        refine ⟨59107672898145474417736265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39405115265430316278490843 59107672898145474417736265)
        ·
          refine ⟨44330754673609105813302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59107672898145474417736265 44330754673609105813302199)
          ·
            refine ⟨66496132010413658719953299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44330754673609105813302199 66496132010413658719953299)
            ·
              refine ⟨99744198015620488079929949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66496132010413658719953299 99744198015620488079929949)
              ·
                refine ⟨37404074255857683029973731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99744198015620488079929949 37404074255857683029973731)
                ·
                  refine ⟨56106111383786524544960597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37404074255857683029973731 56106111383786524544960597)
                  ·
                    refine ⟨657493492778748334511257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56106111383786524544960597 657493492778748334511257)
                    ·
                      rfl

theorem cell22_1920696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_1920696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920696 prefixEnd_1920696 := by exact prefixLift 1920696
  have htrace : WordTrace (prefixWord ++ tailWord_1920696) baseStart_1920696 baseEnd_1920696 := by
    simpa [prefixWord, tailWord_1920696, baseEnd_1920696] using wordTrace_append hprefix tailTrace_1920696
  have hstable : (prefixWord ++ tailWord_1920696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920696).length < 2 ^ (prefixWord ++ tailWord_1920696).sum := by decide
  have hdescent : baseEnd_1920696 < baseStart_1920696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920717 : List Nat := [1, 6, 2, 1, 1, 1, 4, 6]
def baseStart_1920717 : Nat := 118140960795 + 1920717 * 2 ^ 59
def prefixEnd_1920717 : Nat := 4983230072969 + 3 ^ 40 * 1920717 * 2
def baseEnd_1920717 : Nat := 73055631278656808859577

theorem tailTrace_1920717 : CollatzResearch.WordTrace tailWord_1920717 prefixEnd_1920717 73055631278656808859577 := by
  unfold tailWord_1920717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70054304182577816192720405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702869455051877461813603 70054304182577816192720405)
  ·
    refine ⟨3283795508558335134033769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70054304182577816192720405 3283795508558335134033769)
    ·
      refine ⟨2462846631418751350525327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283795508558335134033769 2462846631418751350525327)
      ·
        refine ⟨3694269947128127025787991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462846631418751350525327 3694269947128127025787991)
        ·
          refine ⟨5541404920692190538681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694269947128127025787991 5541404920692190538681987)
          ·
            refine ⟨8312107381038285808022981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541404920692190538681987 8312107381038285808022981)
            ·
              refine ⟨1558520133944678589004309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8312107381038285808022981 1558520133944678589004309)
              ·
                refine ⟨73055631278656808859577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1558520133944678589004309 73055631278656808859577)
                ·
                  rfl

theorem cell22_1920717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 6].length) (baseStart_1920717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920717 prefixEnd_1920717 := by exact prefixLift 1920717
  have htrace : WordTrace (prefixWord ++ tailWord_1920717) baseStart_1920717 baseEnd_1920717 := by
    simpa [prefixWord, tailWord_1920717, baseEnd_1920717] using wordTrace_append hprefix tailTrace_1920717
  have hstable : (prefixWord ++ tailWord_1920717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920717).length < 2 ^ (prefixWord ++ tailWord_1920717).sum := by decide
  have hdescent : baseEnd_1920717 < baseStart_1920717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920822 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1920822 : Nat := 118140960795 + 1920822 * 2 ^ 59
def prefixEnd_1920822 : Nat := 4983230072969 + 3 ^ 40 * 1920822 * 2
def baseEnd_1920822 : Nat := 657536625153726005860871

theorem tailTrace_1920822 : CollatzResearch.WordTrace tailWord_1920822 prefixEnd_1920822 657536625153726005860871 := by
  unfold tailWord_1920822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378633365449838695330795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46705422564798279416861813 4378633365449838695330795)
  ·
    refine ⟨6567950048174758042996193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378633365449838695330795 6567950048174758042996193)
    ·
      refine ⟨4925962536131068532247145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6567950048174758042996193 4925962536131068532247145)
      ·
        refine ⟨3694471902098301399185359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4925962536131068532247145 3694471902098301399185359)
        ·
          refine ⟨5541707853147452098778039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694471902098301399185359 5541707853147452098778039)
          ·
            refine ⟨8312561779721178148167059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541707853147452098778039 8312561779721178148167059)
            ·
              refine ⟨12468842669581767222250589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312561779721178148167059 12468842669581767222250589)
              ·
                refine ⟨4675816001093162708343971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12468842669581767222250589 4675816001093162708343971)
                ·
                  refine ⟨7013724001639744062515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675816001093162708343971 7013724001639744062515957)
                  ·
                    refine ⟨657536625153726005860871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7013724001639744062515957 657536625153726005860871)
                    ·
                      rfl

theorem cell22_1920822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1920822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920822 prefixEnd_1920822 := by exact prefixLift 1920822
  have htrace : WordTrace (prefixWord ++ tailWord_1920822) baseStart_1920822 baseEnd_1920822 := by
    simpa [prefixWord, tailWord_1920822, baseEnd_1920822] using wordTrace_append hprefix tailTrace_1920822
  have hstable : (prefixWord ++ tailWord_1920822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920822).length < 2 ^ (prefixWord ++ tailWord_1920822).sum := by decide
  have hdescent : baseEnd_1920822 < baseStart_1920822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920835 : List Nat := [1, 1, 1, 3, 1, 6, 3, 6]
def baseStart_1920835 : Nat := 118140960795 + 1920835 * 2 ^ 59
def prefixEnd_1920835 : Nat := 4983230072969 + 3 ^ 40 * 1920835 * 2
def baseEnd_1920835 : Nat := 73060119479933145031759

theorem tailTrace_1920835 : CollatzResearch.WordTrace tailWord_1920835 prefixEnd_1920835 73060119479933145031759 := by
  unfold tailWord_1920835
  simp only [CollatzResearch.WordTrace]
  refine ⟨70058607996150322345515959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46705738664100214897010639 70058607996150322345515959)
  ·
    refine ⟨105087911994225483518273939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70058607996150322345515959 105087911994225483518273939)
    ·
      refine ⟨157631867991338225277410909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105087911994225483518273939 157631867991338225277410909)
      ·
        refine ⟨59111950496751834479029091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157631867991338225277410909 59111950496751834479029091)
        ·
          refine ⟨88667925745127751718543637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59111950496751834479029091 88667925745127751718543637)
          ·
            refine ⟨4156309019302863361806733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88667925745127751718543637 4156309019302863361806733)
            ·
              refine ⟨1558615882238573760677525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4156309019302863361806733 1558615882238573760677525)
              ·
                refine ⟨73060119479933145031759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1558615882238573760677525 73060119479933145031759)
                ·
                  rfl

theorem cell22_1920835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 6].length) (baseStart_1920835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920835 prefixEnd_1920835 := by exact prefixLift 1920835
  have htrace : WordTrace (prefixWord ++ tailWord_1920835) baseStart_1920835 baseEnd_1920835 := by
    simpa [prefixWord, tailWord_1920835, baseEnd_1920835] using wordTrace_append hprefix tailTrace_1920835
  have hstable : (prefixWord ++ tailWord_1920835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920835).length < 2 ^ (prefixWord ++ tailWord_1920835).sum := by decide
  have hdescent : baseEnd_1920835 < baseStart_1920835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920886 : List Nat := [5, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1920886 : Nat := 118140960795 + 1920886 * 2 ^ 59
def prefixEnd_1920886 : Nat := 4983230072969 + 3 ^ 40 * 1920886 * 2
def baseEnd_1920886 : Nat := 73062059295739019140075

theorem tailTrace_1920886 : CollatzResearch.WordTrace tailWord_1920886 prefixEnd_1920886 73062059295739019140075 := by
  unfold tailWord_1920886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378779257435347378476407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46706978745977038703748341 4378779257435347378476407)
  ·
    refine ⟨6568168886153021067714611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378779257435347378476407 6568168886153021067714611)
    ·
      refine ⟨9852253329229531601571917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6568168886153021067714611 9852253329229531601571917)
      ·
        refine ⟨3694594998461074350589469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9852253329229531601571917 3694594998461074350589469)
        ·
          refine ⟨1385473124422902881471051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3694594998461074350589469 1385473124422902881471051)
          ·
            refine ⟨2078209686634354322206577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385473124422902881471051 2078209686634354322206577)
            ·
              refine ⟨1558657264975765741654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078209686634354322206577 1558657264975765741654933)
              ·
                refine ⟨73062059295739019140075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1558657264975765741654933 73062059295739019140075)
                ·
                  rfl

theorem cell22_1920886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1920886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920886 prefixEnd_1920886 := by exact prefixLift 1920886
  have htrace : WordTrace (prefixWord ++ tailWord_1920886) baseStart_1920886 baseEnd_1920886 := by
    simpa [prefixWord, tailWord_1920886, baseEnd_1920886] using wordTrace_append hprefix tailTrace_1920886
  have hstable : (prefixWord ++ tailWord_1920886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920886).length < 2 ^ (prefixWord ++ tailWord_1920886).sum := by decide
  have hdescent : baseEnd_1920886 < baseStart_1920886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920955 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_1920955 : Nat := 118140960795 + 1920955 * 2 ^ 59
def prefixEnd_1920955 : Nat := 4983230072969 + 3 ^ 40 * 1920955 * 2
def baseEnd_1920955 : Nat := 657582153771757992285463

theorem tailTrace_1920955 : CollatzResearch.WordTrace tailWord_1920955 prefixEnd_1920955 657582153771757992285463 := by
  unfold tailWord_1920955
  simp only [CollatzResearch.WordTrace]
  refine ⟨70062984755715582839884319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46708656503810388559922879 70062984755715582839884319)
  ·
    refine ⟨105094477133573374259826479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70062984755715582839884319 105094477133573374259826479)
    ·
      refine ⟨157641715700360061389739719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105094477133573374259826479 157641715700360061389739719)
      ·
        refine ⟨236462573550540092084609579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157641715700360061389739719 236462573550540092084609579)
        ·
          refine ⟨354693860325810138126914369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236462573550540092084609579 354693860325810138126914369)
          ·
            refine ⟨266020395244357603595185777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354693860325810138126914369 266020395244357603595185777)
            ·
              refine ⟨199515296433268202696389333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266020395244357603595185777 199515296433268202696389333)
              ·
                refine ⟨4676139760154723500696625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199515296433268202696389333 4676139760154723500696625)
                ·
                  refine ⟨3507104820116042625522469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4676139760154723500696625 3507104820116042625522469)
                  ·
                    refine ⟨657582153771757992285463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507104820116042625522469 657582153771757992285463)
                    ·
                      rfl

theorem cell22_1920955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_1920955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920955 prefixEnd_1920955 := by exact prefixLift 1920955
  have htrace : WordTrace (prefixWord ++ tailWord_1920955) baseStart_1920955 baseEnd_1920955 := by
    simpa [prefixWord, tailWord_1920955, baseEnd_1920955] using wordTrace_append hprefix tailTrace_1920955
  have hstable : (prefixWord ++ tailWord_1920955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920955).length < 2 ^ (prefixWord ++ tailWord_1920955).sum := by decide
  have hdescent : baseEnd_1920955 < baseStart_1920955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920957 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1920957 : Nat := 118140960795 + 1920957 * 2 ^ 59
def prefixEnd_1920957 : Nat := 4983230072969 + 3 ^ 40 * 1920957 * 2
def baseEnd_1920957 : Nat := 657582838412630653735457

theorem tailTrace_1920957 : CollatzResearch.WordTrace tailWord_1920957 prefixEnd_1920957 657582838412630653735457 := by
  unfold tailWord_1920957
  simp only [CollatzResearch.WordTrace]
  refine ⟨70063057701708337181457125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46708705134472224787638083 70063057701708337181457125)
  ·
    refine ⟨13136823319070313221523211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70063057701708337181457125 13136823319070313221523211)
    ·
      refine ⟨19705234978605469832284817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13136823319070313221523211 19705234978605469832284817)
      ·
        refine ⟨14778926233954102374213613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19705234978605469832284817 14778926233954102374213613)
        ·
          refine ⟨5542097337732788390330105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14778926233954102374213613 5542097337732788390330105)
          ·
            refine ⟨4156573003299591292747579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542097337732788390330105 4156573003299591292747579)
            ·
              refine ⟨6234859504949386939121369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156573003299591292747579 6234859504949386939121369)
              ·
                refine ⟨4676144628712040204341027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234859504949386939121369 4676144628712040204341027)
                ·
                  refine ⟨7014216943068060306511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676144628712040204341027 7014216943068060306511541)
                  ·
                    refine ⟨657582838412630653735457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7014216943068060306511541 657582838412630653735457)
                    ·
                      rfl

theorem cell22_1920957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1920957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920957 prefixEnd_1920957 := by exact prefixLift 1920957
  have htrace : WordTrace (prefixWord ++ tailWord_1920957) baseStart_1920957 baseEnd_1920957 := by
    simpa [prefixWord, tailWord_1920957, baseEnd_1920957] using wordTrace_append hprefix tailTrace_1920957
  have hstable : (prefixWord ++ tailWord_1920957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920957).length < 2 ^ (prefixWord ++ tailWord_1920957).sum := by decide
  have hdescent : baseEnd_1920957 < baseStart_1920957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920972 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_1920972 : Nat := 118140960795 + 1920972 * 2 ^ 59
def prefixEnd_1920972 : Nat := 4983230072969 + 3 ^ 40 * 1920972 * 2
def baseEnd_1920972 : Nat := 657587973219175614610411

theorem tailTrace_1920972 : CollatzResearch.WordTrace tailWord_1920972 prefixEnd_1920972 657587973219175614610411 := by
  unfold tailWord_1920972
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031802398326997371626585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46709069864435996495502113 35031802398326997371626585)
  ·
    refine ⟨26273851798745248028719939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35031802398326997371626585 26273851798745248028719939)
    ·
      refine ⟨39410777698117872043079909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26273851798745248028719939 39410777698117872043079909)
      ·
        refine ⟨7389520818397101008077483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39410777698117872043079909 7389520818397101008077483)
        ·
          refine ⟨11084281227595651512116225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389520818397101008077483 11084281227595651512116225)
          ·
            refine ⟨8313210920696738634087169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11084281227595651512116225 8313210920696738634087169)
            ·
              refine ⟨6234908190522553975565377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8313210920696738634087169 6234908190522553975565377)
              ·
                refine ⟨4676181142891915481674033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234908190522553975565377 4676181142891915481674033)
                ·
                  refine ⟨3507135857168936611255525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4676181142891915481674033 3507135857168936611255525)
                  ·
                    refine ⟨657587973219175614610411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507135857168936611255525 657587973219175614610411)
                    ·
                      rfl

theorem cell22_1920972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_1920972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920972 prefixEnd_1920972 := by exact prefixLift 1920972
  have htrace : WordTrace (prefixWord ++ tailWord_1920972) baseStart_1920972 baseEnd_1920972 := by
    simpa [prefixWord, tailWord_1920972, baseEnd_1920972] using wordTrace_append hprefix tailTrace_1920972
  have hstable : (prefixWord ++ tailWord_1920972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920972).length < 2 ^ (prefixWord ++ tailWord_1920972).sum := by decide
  have hdescent : baseEnd_1920972 < baseStart_1920972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920974 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1920974 : Nat := 118140960795 + 1920974 * 2 ^ 59
def prefixEnd_1920974 : Nat := 4983230072969 + 3 ^ 40 * 1920974 * 2
def baseEnd_1920974 : Nat := 657588657860048276060405

theorem tailTrace_1920974 : CollatzResearch.WordTrace tailWord_1920974 prefixEnd_1920974 657588657860048276060405 := by
  unfold tailWord_1920974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757959717830843635603247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46709118495097832723217317 8757959717830843635603247)
  ·
    refine ⟨13136939576746265453404871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8757959717830843635603247 13136939576746265453404871)
    ·
      refine ⟨19705409365119398180107307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13136939576746265453404871 19705409365119398180107307)
      ·
        refine ⟨29558114047679097270160961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19705409365119398180107307 29558114047679097270160961)
        ·
          refine ⟨22168585535759322952620721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29558114047679097270160961 22168585535759322952620721)
          ·
            refine ⟨16626439151819492214465541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22168585535759322952620721 16626439151819492214465541)
            ·
              refine ⟨3117457340966154790212289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16626439151819492214465541 3117457340966154790212289)
              ·
                refine ⟨2338093005724616092659217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3117457340966154790212289 2338093005724616092659217)
                ·
                  refine ⟨1753569754293462069494413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338093005724616092659217 1753569754293462069494413)
                  ·
                    refine ⟨657588657860048276060405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1753569754293462069494413 657588657860048276060405)
                    ·
                      rfl

theorem cell22_1920974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1920974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1920974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1920974 prefixEnd_1920974 := by exact prefixLift 1920974
  have htrace : WordTrace (prefixWord ++ tailWord_1920974) baseStart_1920974 baseEnd_1920974 := by
    simpa [prefixWord, tailWord_1920974, baseEnd_1920974] using wordTrace_append hprefix tailTrace_1920974
  have hstable : (prefixWord ++ tailWord_1920974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920974).length < 2 ^ (prefixWord ++ tailWord_1920974).sum := by decide
  have hdescent : baseEnd_1920974 < baseStart_1920974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921000 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1921000 : Nat := 118140960795 + 1921000 * 2 ^ 59
def prefixEnd_1921000 : Nat := 4983230072969 + 3 ^ 40 * 1921000 * 2
def baseEnd_1921000 : Nat := 657597558191392874910325

theorem tailTrace_1921000 : CollatzResearch.WordTrace tailWord_1921000 prefixEnd_1921000 657597558191392874910325 := by
  unfold tailWord_1921000
  simp only [CollatzResearch.WordTrace]
  refine ⟨35032313020276277762636227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46709750693701703683514969 35032313020276277762636227)
  ·
    refine ⟨52548469530414416643954341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35032313020276277762636227 52548469530414416643954341)
    ·
      refine ⟨9852838036952703120741439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52548469530414416643954341 9852838036952703120741439)
      ·
        refine ⟨14779257055429054681112159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9852838036952703120741439 14779257055429054681112159)
        ·
          refine ⟨22168885583143582021668239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14779257055429054681112159 22168885583143582021668239)
          ·
            refine ⟨33253328374715373032502359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22168885583143582021668239 33253328374715373032502359)
            ·
              refine ⟨49879992562073059548753539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33253328374715373032502359 49879992562073059548753539)
              ·
                refine ⟨74819988843109589323130309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49879992562073059548753539 74819988843109589323130309)
                ·
                  refine ⟨14028747908083047998086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74819988843109589323130309 14028747908083047998086933)
                  ·
                    refine ⟨657597558191392874910325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14028747908083047998086933 657597558191392874910325)
                    ·
                      rfl

theorem cell22_1921000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1921000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921000 prefixEnd_1921000 := by exact prefixLift 1921000
  have htrace : WordTrace (prefixWord ++ tailWord_1921000) baseStart_1921000 baseEnd_1921000 := by
    simpa [prefixWord, tailWord_1921000, baseEnd_1921000] using wordTrace_append hprefix tailTrace_1921000
  have hstable : (prefixWord ++ tailWord_1921000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921000).length < 2 ^ (prefixWord ++ tailWord_1921000).sum := by decide
  have hdescent : baseEnd_1921000 < baseStart_1921000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921019 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 1, 3]
def baseStart_1921019 : Nat := 118140960795 + 1921019 * 2 ^ 59
def prefixEnd_1921019 : Nat := 4983230072969 + 3 ^ 40 * 1921019 * 2
def baseEnd_1921019 : Nat := 657604062279683158685267

theorem tailTrace_1921019 : CollatzResearch.WordTrace tailWord_1921019 prefixEnd_1921019 657604062279683158685267 := by
  unfold tailWord_1921019
  simp only [CollatzResearch.WordTrace]
  refine ⟨70065319027483721770214111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46710212684989147846809407 70065319027483721770214111)
  ·
    refine ⟨105097978541225582655321167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70065319027483721770214111 105097978541225582655321167)
    ·
      refine ⟨157646967811838373982981751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105097978541225582655321167 157646967811838373982981751)
      ·
        refine ⟨236470451717757560974472627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157646967811838373982981751 236470451717757560974472627)
        ·
          refine ⟨354705677576636341461708941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236470451717757560974472627 354705677576636341461708941)
          ·
            refine ⟨133014629091238628048140853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354705677576636341461708941 133014629091238628048140853)
            ·
              refine ⟨12470121477303621379513205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133014629091238628048140853 12470121477303621379513205)
              ·
                refine ⟨1169073888497214504329363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12470121477303621379513205 1169073888497214504329363)
                ·
                  refine ⟨1753610832745821756494045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169073888497214504329363 1753610832745821756494045)
                  ·
                    refine ⟨657604062279683158685267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1753610832745821756494045 657604062279683158685267)
                    ·
                      rfl

theorem cell22_1921019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 3].length) (baseStart_1921019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921019 prefixEnd_1921019 := by exact prefixLift 1921019
  have htrace : WordTrace (prefixWord ++ tailWord_1921019) baseStart_1921019 baseEnd_1921019 := by
    simpa [prefixWord, tailWord_1921019, baseEnd_1921019] using wordTrace_append hprefix tailTrace_1921019
  have hstable : (prefixWord ++ tailWord_1921019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921019).length < 2 ^ (prefixWord ++ tailWord_1921019).sum := by decide
  have hdescent : baseEnd_1921019 < baseStart_1921019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921259 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_1921259 : Nat := 118140960795 + 1921259 * 2 ^ 59
def prefixEnd_1921259 : Nat := 4983230072969 + 3 ^ 40 * 1921259 * 2
def baseEnd_1921259 : Nat := 657686219184402532684531

theorem tailTrace_1921259 : CollatzResearch.WordTrace tailWord_1921259 prefixEnd_1921259 657686219184402532684531 := by
  unfold tailWord_1921259
  simp only [CollatzResearch.WordTrace]
  refine ⟨70074072546614242758950831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46716048364409495172633887 70074072546614242758950831)
  ·
    refine ⟨105111108819921364138426247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70074072546614242758950831 105111108819921364138426247)
    ·
      refine ⟨157666663229882046207639371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105111108819921364138426247 157666663229882046207639371)
      ·
        refine ⟨236499994844823069311459057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157666663229882046207639371 236499994844823069311459057)
        ·
          refine ⟨177374996133617301983594293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236499994844823069311459057 177374996133617301983594293)
          ·
            refine ⟨16628905887526622060961965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177374996133617301983594293 16628905887526622060961965)
            ·
              refine ⟨6235839707822483272860737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16628905887526622060961965 6235839707822483272860737)
              ·
                refine ⟨4676879780866862454645553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6235839707822483272860737 4676879780866862454645553)
                ·
                  refine ⟨3507659835650146840984165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4676879780866862454645553 3507659835650146840984165)
                  ·
                    refine ⟨657686219184402532684531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3507659835650146840984165 657686219184402532684531)
                    ·
                      rfl

theorem cell22_1921259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_1921259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921259 prefixEnd_1921259 := by exact prefixLift 1921259
  have htrace : WordTrace (prefixWord ++ tailWord_1921259) baseStart_1921259 baseEnd_1921259 := by
    simpa [prefixWord, tailWord_1921259, baseEnd_1921259] using wordTrace_append hprefix tailTrace_1921259
  have hstable : (prefixWord ++ tailWord_1921259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921259).length < 2 ^ (prefixWord ++ tailWord_1921259).sum := by decide
  have hdescent : baseEnd_1921259 < baseStart_1921259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921263 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 4]
def baseStart_1921263 : Nat := 118140960795 + 1921263 * 2 ^ 59
def prefixEnd_1921263 : Nat := 4983230072969 + 3 ^ 40 * 1921263 * 2
def baseEnd_1921263 : Nat := 219229196155382618528173

theorem tailTrace_1921263 : CollatzResearch.WordTrace tailWord_1921263 prefixEnd_1921263 219229196155382618528173 := by
  unfold tailWord_1921263
  simp only [CollatzResearch.WordTrace]
  refine ⟨70074218438599751442096443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46716145625733167628064295 70074218438599751442096443)
  ·
    refine ⟨105111327657899627163144665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70074218438599751442096443 105111327657899627163144665)
    ·
      refine ⟨78833495743424720372358499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105111327657899627163144665 78833495743424720372358499)
      ·
        refine ⟨118250243615137080558537749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78833495743424720372358499 118250243615137080558537749)
        ·
          refine ⟨5542980169459550651181457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118250243615137080558537749 5542980169459550651181457)
          ·
            refine ⟨4157235127094662988386093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542980169459550651181457 4157235127094662988386093)
            ·
              refine ⟨1558963172660498620644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4157235127094662988386093 1558963172660498620644785)
              ·
                refine ⟨1169222379495373965483589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558963172660498620644785 1169222379495373965483589)
                ·
                  refine ⟨219229196155382618528173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169222379495373965483589 219229196155382618528173)
                  ·
                    rfl

theorem cell22_1921263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 4].length) (baseStart_1921263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921263 prefixEnd_1921263 := by exact prefixLift 1921263
  have htrace : WordTrace (prefixWord ++ tailWord_1921263) baseStart_1921263 baseEnd_1921263 := by
    simpa [prefixWord, tailWord_1921263, baseEnd_1921263] using wordTrace_append hprefix tailTrace_1921263
  have hstable : (prefixWord ++ tailWord_1921263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921263).length < 2 ^ (prefixWord ++ tailWord_1921263).sum := by decide
  have hdescent : baseEnd_1921263 < baseStart_1921263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921274 : List Nat := [3, 1, 1, 1, 1, 6, 2, 7]
def baseStart_1921274 : Nat := 118140960795 + 1921274 * 2 ^ 59
def prefixEnd_1921274 : Nat := 4983230072969 + 3 ^ 40 * 1921274 * 2
def baseEnd_1921274 : Nat := 73076817110105277062165

theorem tailTrace_1921274 : CollatzResearch.WordTrace tailWord_1921274 prefixEnd_1921274 73076817110105277062165 := by
  unfold tailWord_1921274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518654910389975080186719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46716413094373266880497917 17518654910389975080186719)
  ·
    refine ⟨26277982365584962620280079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17518654910389975080186719 26277982365584962620280079)
    ·
      refine ⟨39416973548377443930420119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26277982365584962620280079 39416973548377443930420119)
      ·
        refine ⟨59125460322566165895630179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39416973548377443930420119 59125460322566165895630179)
        ·
          refine ⟨88688190483849248843445269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59125460322566165895630179 88688190483849248843445269)
          ·
            refine ⟨4157258928930433539536497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88688190483849248843445269 4157258928930433539536497)
            ·
              refine ⟨3117944196697825154652373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157258928930433539536497 3117944196697825154652373)
              ·
                refine ⟨73076817110105277062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3117944196697825154652373 73076817110105277062165)
                ·
                  rfl

theorem cell22_1921274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_1921274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921274 prefixEnd_1921274 := by exact prefixLift 1921274
  have htrace : WordTrace (prefixWord ++ tailWord_1921274) baseStart_1921274 baseEnd_1921274 := by
    simpa [prefixWord, tailWord_1921274, baseEnd_1921274] using wordTrace_append hprefix tailTrace_1921274
  have hstable : (prefixWord ++ tailWord_1921274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921274).length < 2 ^ (prefixWord ++ tailWord_1921274).sum := by decide
  have hdescent : baseEnd_1921274 < baseStart_1921274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921278 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1921278 : Nat := 118140960795 + 1921278 * 2 ^ 59
def prefixEnd_1921278 : Nat := 4983230072969 + 3 ^ 40 * 1921278 * 2
def baseEnd_1921278 : Nat := 657692723272692816459473

theorem tailTrace_1921278 : CollatzResearch.WordTrace tailWord_1921278 prefixEnd_1921278 657692723272692816459473 := by
  unfold tailWord_1921278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759345691693176125486561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46716510355696939335928325 8759345691693176125486561)
  ·
    refine ⟨6569509268769882094114921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8759345691693176125486561 6569509268769882094114921)
    ·
      refine ⟨4927131951577411570586191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6569509268769882094114921 4927131951577411570586191)
      ·
        refine ⟨7390697927366117355879287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927131951577411570586191 7390697927366117355879287)
        ·
          refine ⟨11086046891049176033818931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390697927366117355879287 11086046891049176033818931)
          ·
            refine ⟨16629070336573764050728397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086046891049176033818931 16629070336573764050728397)
            ·
              refine ⟨6235901376215161519023149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16629070336573764050728397 6235901376215161519023149)
              ·
                refine ⟨2338463016080685569633681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6235901376215161519023149 2338463016080685569633681)
                ·
                  refine ⟨1753847262060514177225261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338463016080685569633681 1753847262060514177225261)
                  ·
                    refine ⟨657692723272692816459473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1753847262060514177225261 657692723272692816459473)
                    ·
                      rfl

theorem cell22_1921278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1921278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921278 prefixEnd_1921278 := by exact prefixLift 1921278
  have htrace : WordTrace (prefixWord ++ tailWord_1921278) baseStart_1921278 baseEnd_1921278 := by
    simpa [prefixWord, tailWord_1921278, baseEnd_1921278] using wordTrace_append hprefix tailTrace_1921278
  have hstable : (prefixWord ++ tailWord_1921278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921278).length < 2 ^ (prefixWord ++ tailWord_1921278).sum := by decide
  have hdescent : baseEnd_1921278 < baseStart_1921278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921325 : List Nat := [1, 5, 3, 1, 3, 1, 1, 7]
def baseStart_1921325 : Nat := 118140960795 + 1921325 * 2 ^ 59
def prefixEnd_1921325 : Nat := 4983230072969 + 3 ^ 40 * 1921325 * 2
def baseEnd_1921325 : Nat := 73078756925911151170481

theorem tailTrace_1921325 : CollatzResearch.WordTrace tailWord_1921325 prefixEnd_1921325 73078756925911151170481 := by
  unfold tailWord_1921325
  simp only [CollatzResearch.WordTrace]
  refine ⟨70076479764375136030853429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46717653176250090687235619 70076479764375136030853429)
  ·
    refine ⟨6569669977910169002892509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70076479764375136030853429 6569669977910169002892509)
    ·
      refine ⟨2463626241716313376084691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6569669977910169002892509 2463626241716313376084691)
      ·
        refine ⟨3695439362574470064127037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463626241716313376084691 3695439362574470064127037)
        ·
          refine ⟨1385789760965426274047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3695439362574470064127037 1385789760965426274047639)
          ·
            refine ⟨2078684641448139411071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385789760965426274047639 2078684641448139411071459)
            ·
              refine ⟨3118026962172209116607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078684641448139411071459 3118026962172209116607189)
              ·
                refine ⟨73078756925911151170481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3118026962172209116607189 73078756925911151170481)
                ·
                  rfl

theorem cell22_1921325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 7].length) (baseStart_1921325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921325 prefixEnd_1921325 := by exact prefixLift 1921325
  have htrace : WordTrace (prefixWord ++ tailWord_1921325) baseStart_1921325 baseEnd_1921325 := by
    simpa [prefixWord, tailWord_1921325, baseEnd_1921325] using wordTrace_append hprefix tailTrace_1921325
  have hstable : (prefixWord ++ tailWord_1921325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921325).length < 2 ^ (prefixWord ++ tailWord_1921325).sum := by decide
  have hdescent : baseEnd_1921325 < baseStart_1921325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921381 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1921381 : Nat := 118140960795 + 1921381 * 2 ^ 59
def prefixEnd_1921381 : Nat := 4983230072969 + 3 ^ 40 * 1921381 * 2
def baseEnd_1921381 : Nat := 219242660759211627044719

theorem tailTrace_1921381 : CollatzResearch.WordTrace tailWord_1921381 prefixEnd_1921381 219242660759211627044719 := by
  unfold tailWord_1921381
  simp only [CollatzResearch.WordTrace]
  refine ⟨70078522252172257594891997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46719014834781505063261331 70078522252172257594891997)
  ·
    refine ⟨26279445844564596598084499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70078522252172257594891997 26279445844564596598084499)
    ·
      refine ⟨39419168766846894897126749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26279445844564596598084499 39419168766846894897126749)
      ·
        refine ⟨14782188287567585586422531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39419168766846894897126749 14782188287567585586422531)
        ·
          refine ⟨22173282431351378379633797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14782188287567585586422531 22173282431351378379633797)
          ·
            refine ⟨4157490455878383446181337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22173282431351378379633797 4157490455878383446181337)
            ·
              refine ⟨3118117841908787584636003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157490455878383446181337 3118117841908787584636003)
              ·
                refine ⟨4677176762863181376954005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118117841908787584636003 4677176762863181376954005)
                ·
                  refine ⟨219242660759211627044719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4677176762863181376954005 219242660759211627044719)
                  ·
                    rfl

theorem cell22_1921381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1921381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921381 prefixEnd_1921381 := by exact prefixLift 1921381
  have htrace : WordTrace (prefixWord ++ tailWord_1921381) baseStart_1921381 baseEnd_1921381 := by
    simpa [prefixWord, tailWord_1921381, baseEnd_1921381] using wordTrace_append hprefix tailTrace_1921381
  have hstable : (prefixWord ++ tailWord_1921381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921381).length < 2 ^ (prefixWord ++ tailWord_1921381).sum := by decide
  have hdescent : baseEnd_1921381 < baseStart_1921381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921447 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1921447 : Nat := 118140960795 + 1921447 * 2 ^ 59
def prefixEnd_1921447 : Nat := 4983230072969 + 3 ^ 40 * 1921447 * 2
def baseEnd_1921447 : Nat := 657750575426432708983955

theorem tailTrace_1921447 : CollatzResearch.WordTrace tailWord_1921447 prefixEnd_1921447 657750575426432708983955 := by
  unfold tailWord_1921447
  simp only [CollatzResearch.WordTrace]
  refine ⟨70080929469933150866794595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46720619646622100577863063 70080929469933150866794595)
  ·
    refine ⟨105121394204899726300191893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70080929469933150866794595 105121394204899726300191893)
    ·
      refine ⟨4927565353354674670321495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105121394204899726300191893 4927565353354674670321495)
      ·
        refine ⟨7391348030032012005482243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927565353354674670321495 7391348030032012005482243)
        ·
          refine ⟨11087022045048018008223365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391348030032012005482243 11087022045048018008223365)
          ·
            refine ⟨2078816633446503376541881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11087022045048018008223365 2078816633446503376541881)
            ·
              refine ⟨1559112475084877532406411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078816633446503376541881 1559112475084877532406411)
              ·
                refine ⟨2338668712627316298609617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559112475084877532406411 2338668712627316298609617)
                ·
                  refine ⟨1754001534470487223957213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338668712627316298609617 1754001534470487223957213)
                  ·
                    refine ⟨657750575426432708983955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754001534470487223957213 657750575426432708983955)
                    ·
                      rfl

theorem cell22_1921447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1921447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921447 prefixEnd_1921447 := by exact prefixLift 1921447
  have htrace : WordTrace (prefixWord ++ tailWord_1921447) baseStart_1921447 baseEnd_1921447 := by
    simpa [prefixWord, tailWord_1921447, baseEnd_1921447] using wordTrace_append hprefix tailTrace_1921447
  have hstable : (prefixWord ++ tailWord_1921447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921447).length < 2 ^ (prefixWord ++ tailWord_1921447).sum := by decide
  have hdescent : baseEnd_1921447 < baseStart_1921447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921486 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1921486 : Nat := 118140960795 + 1921486 * 2 ^ 59
def prefixEnd_1921486 : Nat := 4983230072969 + 3 ^ 40 * 1921486 * 2
def baseEnd_1921486 : Nat := 657763925923449607258835

theorem tailTrace_1921486 : CollatzResearch.WordTrace tailWord_1921486 prefixEnd_1921486 657763925923449607258835 := by
  unfold tailWord_1921486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760293989598982565933039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46721567944527907018309541 8760293989598982565933039)
  ·
    refine ⟨13140440984398473848899559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760293989598982565933039 13140440984398473848899559)
    ·
      refine ⟨19710661476597710773349339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13140440984398473848899559 19710661476597710773349339)
      ·
        refine ⟨29565992214896566160024009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19710661476597710773349339 29565992214896566160024009)
        ·
          refine ⟨22174494161172424620018007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29565992214896566160024009 22174494161172424620018007)
          ·
            refine ⟨33261741241758636930027011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22174494161172424620018007 33261741241758636930027011)
            ·
              refine ⟨49892611862637955395040517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33261741241758636930027011 49892611862637955395040517)
              ·
                refine ⟨9354864724244616636570097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49892611862637955395040517 9354864724244616636570097)
                ·
                  refine ⟨7016148543183462477427573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9354864724244616636570097 7016148543183462477427573)
                  ·
                    refine ⟨657763925923449607258835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7016148543183462477427573 657763925923449607258835)
                    ·
                      rfl

theorem cell22_1921486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1921486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921486 prefixEnd_1921486 := by exact prefixLift 1921486
  have htrace : WordTrace (prefixWord ++ tailWord_1921486) baseStart_1921486 baseEnd_1921486 := by
    simpa [prefixWord, tailWord_1921486, baseEnd_1921486] using wordTrace_append hprefix tailTrace_1921486
  have hstable : (prefixWord ++ tailWord_1921486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921486).length < 2 ^ (prefixWord ++ tailWord_1921486).sum := by decide
  have hdescent : baseEnd_1921486 < baseStart_1921486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921492 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1921492 : Nat := 118140960795 + 1921492 * 2 ^ 59
def prefixEnd_1921492 : Nat := 4983230072969 + 3 ^ 40 * 1921492 * 2
def baseEnd_1921492 : Nat := 657765979846067591608817

theorem tailTrace_1921492 : CollatzResearch.WordTrace tailWord_1921492 prefixEnd_1921492 657765979846067591608817 := by
  unfold tailWord_1921492
  simp only [CollatzResearch.WordTrace]
  refine ⟨35041285377385061776091365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46721713836513415701455153 35041285377385061776091365)
  ·
    refine ⟨6570241008259699083017131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35041285377385061776091365 6570241008259699083017131)
    ·
      refine ⟨9855361512389548624525697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570241008259699083017131 9855361512389548624525697)
      ·
        refine ⟨7391521134292161468394273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855361512389548624525697 7391521134292161468394273)
        ·
          refine ⟨5543640850719121101295705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7391521134292161468394273 5543640850719121101295705)
          ·
            refine ⟨4157730638039340825971779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543640850719121101295705 4157730638039340825971779)
            ·
              refine ⟨6236595957059011238957669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157730638039340825971779 6236595957059011238957669)
              ·
                refine ⟨1169361741948564607304563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6236595957059011238957669 1169361741948564607304563)
                ·
                  refine ⟨1754042612922846910956845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169361741948564607304563 1754042612922846910956845)
                  ·
                    refine ⟨657765979846067591608817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754042612922846910956845 657765979846067591608817)
                    ·
                      rfl

theorem cell22_1921492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1921492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921492 prefixEnd_1921492 := by exact prefixLift 1921492
  have htrace : WordTrace (prefixWord ++ tailWord_1921492) baseStart_1921492 baseEnd_1921492 := by
    simpa [prefixWord, tailWord_1921492, baseEnd_1921492] using wordTrace_append hprefix tailTrace_1921492
  have hstable : (prefixWord ++ tailWord_1921492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921492).length < 2 ^ (prefixWord ++ tailWord_1921492).sum := by decide
  have hdescent : baseEnd_1921492 < baseStart_1921492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921516 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_1921516 : Nat := 118140960795 + 1921516 * 2 ^ 59
def prefixEnd_1921516 : Nat := 4983230072969 + 3 ^ 40 * 1921516 * 2
def baseEnd_1921516 : Nat := 219258065178846509669581

theorem tailTrace_1921516 : CollatzResearch.WordTrace tailWord_1921516 prefixEnd_1921516 219258065178846509669581 := by
  unfold tailWord_1921516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35041723053341587825528201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46722297404455450434037601 35041723053341587825528201)
  ·
    refine ⟨26281292290006190869146151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35041723053341587825528201 26281292290006190869146151)
    ·
      refine ⟨39421938435009286303719227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26281292290006190869146151 39421938435009286303719227)
      ·
        refine ⟨59132907652513929455578841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39421938435009286303719227 59132907652513929455578841)
        ·
          refine ⟨44349680739385447091684131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59132907652513929455578841 44349680739385447091684131)
          ·
            refine ⟨66524521109078170637526197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44349680739385447091684131 66524521109078170637526197)
            ·
              refine ⟨6236673853976078497268081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66524521109078170637526197 6236673853976078497268081)
              ·
                refine ⟨4677505390482058872951061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6236673853976078497268081 4677505390482058872951061)
                ·
                  refine ⟨219258065178846509669581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4677505390482058872951061 219258065178846509669581)
                  ·
                    rfl

theorem cell22_1921516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_1921516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921516 prefixEnd_1921516 := by exact prefixLift 1921516
  have htrace : WordTrace (prefixWord ++ tailWord_1921516) baseStart_1921516 baseEnd_1921516 := by
    simpa [prefixWord, tailWord_1921516, baseEnd_1921516] using wordTrace_append hprefix tailTrace_1921516
  have hstable : (prefixWord ++ tailWord_1921516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921516).length < 2 ^ (prefixWord ++ tailWord_1921516).sum := by decide
  have hdescent : baseEnd_1921516 < baseStart_1921516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921518 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1921518 : Nat := 118140960795 + 1921518 * 2 ^ 59
def prefixEnd_1921518 : Nat := 4983230072969 + 3 ^ 40 * 1921518 * 2
def baseEnd_1921518 : Nat := 657774880177412190458737

theorem tailTrace_1921518 : CollatzResearch.WordTrace tailWord_1921518 prefixEnd_1921518 657774880177412190458737 := by
  unfold tailWord_1921518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760439881584491249078651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46722346035117286661752805 8760439881584491249078651)
  ·
    refine ⟨13140659822376736873617977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760439881584491249078651 13140659822376736873617977)
    ·
      refine ⟨9855494866782552655213483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140659822376736873617977 9855494866782552655213483)
      ·
        refine ⟨14783242300173828982820225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9855494866782552655213483 14783242300173828982820225)
        ·
          refine ⟨11087431725130371737115169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14783242300173828982820225 11087431725130371737115169)
          ·
            refine ⟨8315573793847778802836377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11087431725130371737115169 8315573793847778802836377)
            ·
              refine ⟨6236680345385834102127283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315573793847778802836377 6236680345385834102127283)
              ·
                refine ⟨9355020518078751153190925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236680345385834102127283 9355020518078751153190925)
                ·
                  refine ⟨3508132694279531682446597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9355020518078751153190925 3508132694279531682446597)
                  ·
                    refine ⟨657774880177412190458737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508132694279531682446597 657774880177412190458737)
                    ·
                      rfl

theorem cell22_1921518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1921518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921518 prefixEnd_1921518 := by exact prefixLift 1921518
  have htrace : WordTrace (prefixWord ++ tailWord_1921518) baseStart_1921518 baseEnd_1921518 := by
    simpa [prefixWord, tailWord_1921518, baseEnd_1921518] using wordTrace_append hprefix tailTrace_1921518
  have hstable : (prefixWord ++ tailWord_1921518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921518).length < 2 ^ (prefixWord ++ tailWord_1921518).sum := by decide
  have hdescent : baseEnd_1921518 < baseStart_1921518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921550 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1921550 : Nat := 118140960795 + 1921550 * 2 ^ 59
def prefixEnd_1921550 : Nat := 4983230072969 + 3 ^ 40 * 1921550 * 2
def baseEnd_1921550 : Nat := 219261944810458257886213

theorem tailTrace_1921550 : CollatzResearch.WordTrace tailWord_1921550 prefixEnd_1921550 219261944810458257886213 := by
  unfold tailWord_1921550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760585773569999932224263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46723124125706666305196069 8760585773569999932224263)
  ·
    refine ⟨13140878660354999898336395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760585773569999932224263 13140878660354999898336395)
    ·
      refine ⟨19711317990532499847504593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13140878660354999898336395 19711317990532499847504593)
      ·
        refine ⟨14783488492899374885628445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19711317990532499847504593 14783488492899374885628445)
        ·
          refine ⟨5543808184837265582110667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14783488492899374885628445 5543808184837265582110667)
          ·
            refine ⟨8315712277255898373166001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543808184837265582110667 8315712277255898373166001)
            ·
              refine ⟨6236784207941923779874501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8315712277255898373166001 6236784207941923779874501)
              ·
                refine ⟨1169397038989110708726469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6236784207941923779874501 1169397038989110708726469)
                ·
                  refine ⟨219261944810458257886213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169397038989110708726469 219261944810458257886213)
                  ·
                    rfl

theorem cell22_1921550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1921550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921550 prefixEnd_1921550 := by exact prefixLift 1921550
  have htrace : WordTrace (prefixWord ++ tailWord_1921550) baseStart_1921550 baseEnd_1921550 := by
    simpa [prefixWord, tailWord_1921550, baseEnd_1921550] using wordTrace_append hprefix tailTrace_1921550
  have hstable : (prefixWord ++ tailWord_1921550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921550).length < 2 ^ (prefixWord ++ tailWord_1921550).sum := by decide
  have hdescent : baseEnd_1921550 < baseStart_1921550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921565 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1921565 : Nat := 118140960795 + 1921565 * 2 ^ 59
def prefixEnd_1921565 : Nat := 4983230072969 + 3 ^ 40 * 1921565 * 2
def baseEnd_1921565 : Nat := 657790969237919734533593

theorem tailTrace_1921565 : CollatzResearch.WordTrace tailWord_1921565 prefixEnd_1921565 657790969237919734533593 := by
  unfold tailWord_1921565
  simp only [CollatzResearch.WordTrace]
  refine ⟨70085233283505657019590149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46723488855670438013060099 70085233283505657019590149)
  ·
    refine ⟨13140981240657310691173153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70085233283505657019590149 13140981240657310691173153)
    ·
      refine ⟨9855735930492983018379865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140981240657310691173153 9855735930492983018379865)
      ·
        refine ⟨7391801947869737263784899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855735930492983018379865 7391801947869737263784899)
        ·
          refine ⟨11087702921804605895677349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391801947869737263784899 11087702921804605895677349)
          ·
            refine ⟨2078944297838363605439503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11087702921804605895677349 2078944297838363605439503)
            ·
              refine ⟨3118416446757545408159255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078944297838363605439503 3118416446757545408159255)
              ·
                refine ⟨4677624670136318112238883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118416446757545408159255 4677624670136318112238883)
                ·
                  refine ⟨7016437005204477168358325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4677624670136318112238883 7016437005204477168358325)
                  ·
                    refine ⟨657790969237919734533593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7016437005204477168358325 657790969237919734533593)
                    ·
                      rfl

theorem cell22_1921565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1921565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921565 prefixEnd_1921565 := by exact prefixLift 1921565
  have htrace : WordTrace (prefixWord ++ tailWord_1921565) baseStart_1921565 baseEnd_1921565 := by
    simpa [prefixWord, tailWord_1921565, baseEnd_1921565] using wordTrace_append hprefix tailTrace_1921565
  have hstable : (prefixWord ++ tailWord_1921565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921565).length < 2 ^ (prefixWord ++ tailWord_1921565).sum := by decide
  have hdescent : baseEnd_1921565 < baseStart_1921565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921578 : List Nat := [3, 1, 4, 1, 1, 3, 1, 8]
def baseStart_1921578 : Nat := 118140960795 + 1921578 * 2 ^ 59
def prefixEnd_1921578 : Nat := 4983230072969 + 3 ^ 40 * 1921578 * 2
def baseEnd_1921578 : Nat := 73088379933732448217617

theorem tailTrace_1921578 : CollatzResearch.WordTrace tailWord_1921578 prefixEnd_1921578 73088379933732448217617 := by
  unfold tailWord_1921578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521426858114640059953347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46723804954972373493208925 17521426858114640059953347)
  ·
    refine ⟨26282140287171960089930021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17521426858114640059953347 26282140287171960089930021)
    ·
      refine ⟨4927901303844742516861879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26282140287171960089930021 4927901303844742516861879)
      ·
        refine ⟨7391851955767113775292819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927901303844742516861879 7391851955767113775292819)
        ·
          refine ⟨11087777933650670662939229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391851955767113775292819 11087777933650670662939229)
          ·
            refine ⟨4157916725119001498602211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11087777933650670662939229 4157916725119001498602211)
            ·
              refine ⟨6236875087678502247903317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157916725119001498602211 6236875087678502247903317)
              ·
                refine ⟨73088379933732448217617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6236875087678502247903317 73088379933732448217617)
                ·
                  rfl

theorem cell22_1921578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_1921578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921578 prefixEnd_1921578 := by exact prefixLift 1921578
  have htrace : WordTrace (prefixWord ++ tailWord_1921578) baseStart_1921578 baseEnd_1921578 := by
    simpa [prefixWord, tailWord_1921578, baseEnd_1921578] using wordTrace_append hprefix tailTrace_1921578
  have hstable : (prefixWord ++ tailWord_1921578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921578).length < 2 ^ (prefixWord ++ tailWord_1921578).sum := by decide
  have hdescent : baseEnd_1921578 < baseStart_1921578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921610 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1921610 : Nat := 118140960795 + 1921610 * 2 ^ 59
def prefixEnd_1921610 : Nat := 4983230072969 + 3 ^ 40 * 1921610 * 2
def baseEnd_1921610 : Nat := 657806373657554617158455

theorem tailTrace_1921610 : CollatzResearch.WordTrace tailWord_1921610 prefixEnd_1921610 657806373657554617158455 := by
  unfold tailWord_1921610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521718642085657426244571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46724583045561753136652189 17521718642085657426244571)
  ·
    refine ⟨26282577963128486139366857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17521718642085657426244571 26282577963128486139366857)
    ·
      refine ⟨19711933472346364604525143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26282577963128486139366857 19711933472346364604525143)
      ·
        refine ⟨29567900208519546906787715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711933472346364604525143 29567900208519546906787715)
        ·
          refine ⟨44351850312779320360181573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29567900208519546906787715 44351850312779320360181573)
          ·
            refine ⟨8315971933646122567534045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44351850312779320360181573 8315971933646122567534045)
            ·
              refine ⟨3118489475117295962825267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8315971933646122567534045 3118489475117295962825267)
              ·
                refine ⟨4677734212675943944237901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118489475117295962825267 4677734212675943944237901)
                ·
                  refine ⟨1754150329753478979089213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4677734212675943944237901 1754150329753478979089213)
                  ·
                    refine ⟨657806373657554617158455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754150329753478979089213 657806373657554617158455)
                    ·
                      rfl

theorem cell22_1921610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1921610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921610 prefixEnd_1921610 := by exact prefixLift 1921610
  have htrace : WordTrace (prefixWord ++ tailWord_1921610) baseStart_1921610 baseEnd_1921610 := by
    simpa [prefixWord, tailWord_1921610, baseEnd_1921610] using wordTrace_append hprefix tailTrace_1921610
  have hstable : (prefixWord ++ tailWord_1921610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921610).length < 2 ^ (prefixWord ++ tailWord_1921610).sum := by decide
  have hdescent : baseEnd_1921610 < baseStart_1921610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921623 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 5]
def baseStart_1921623 : Nat := 118140960795 + 1921623 * 2 ^ 59
def prefixEnd_1921623 : Nat := 4983230072969 + 3 ^ 40 * 1921623 * 2
def baseEnd_1921623 : Nat := 219270274607742305527805

theorem tailTrace_1921623 : CollatzResearch.WordTrace tailWord_1921623 prefixEnd_1921623 219270274607742305527805 := by
  unfold tailWord_1921623
  simp only [CollatzResearch.WordTrace]
  refine ⟨70087348717295532925201523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46724899144863688616801015 70087348717295532925201523)
  ·
    refine ⟨105131023075943299387802285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70087348717295532925201523 105131023075943299387802285)
    ·
      refine ⟨39424133653478737270425857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105131023075943299387802285 39424133653478737270425857)
      ·
        refine ⟨29568100240109052952819393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39424133653478737270425857 29568100240109052952819393)
        ·
          refine ⟨22176075180081789714614545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29568100240109052952819393 22176075180081789714614545)
          ·
            refine ⟨16632056385061342285960909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22176075180081789714614545 16632056385061342285960909)
            ·
              refine ⟨6237021144398003357235341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16632056385061342285960909 6237021144398003357235341)
              ·
                refine ⟨2338882929149251258963253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6237021144398003357235341 2338882929149251258963253)
                ·
                  refine ⟨219270274607742305527805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338882929149251258963253 219270274607742305527805)
                  ·
                    rfl

theorem cell22_1921623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].length) (baseStart_1921623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921623 prefixEnd_1921623 := by exact prefixLift 1921623
  have htrace : WordTrace (prefixWord ++ tailWord_1921623) baseStart_1921623 baseEnd_1921623 := by
    simpa [prefixWord, tailWord_1921623, baseEnd_1921623] using wordTrace_append hprefix tailTrace_1921623
  have hstable : (prefixWord ++ tailWord_1921623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921623).length < 2 ^ (prefixWord ++ tailWord_1921623).sum := by decide
  have hdescent : baseEnd_1921623 < baseStart_1921623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921651 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 10]
def baseStart_1921651 : Nat := 118140960795 + 1921651 * 2 ^ 59
def prefixEnd_1921651 : Nat := 4983230072969 + 3 ^ 40 * 1921651 * 2
def baseEnd_1921651 : Nat := 219273469598481392294443

theorem tailTrace_1921651 : CollatzResearch.WordTrace tailWord_1921651 prefixEnd_1921651 219273469598481392294443 := by
  unfold tailWord_1921651
  simp only [CollatzResearch.WordTrace]
  refine ⟨70088369961194093707220807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46725579974129395804813871 70088369961194093707220807)
  ·
    refine ⟨105132554941791140560831211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70088369961194093707220807 105132554941791140560831211)
    ·
      refine ⟨157698832412686710841246817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105132554941791140560831211 157698832412686710841246817)
      ·
        refine ⟨118274124309515033130935113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157698832412686710841246817 118274124309515033130935113)
        ·
          refine ⟨88705593232136274848201335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118274124309515033130935113 88705593232136274848201335)
          ·
            refine ⟨133058389848204412272302003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88705593232136274848201335 133058389848204412272302003)
            ·
              refine ⟨199587584772306618408453005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133058389848204412272302003 199587584772306618408453005)
              ·
                refine ⟨74845344289614981903169877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199587584772306618408453005 74845344289614981903169877)
                ·
                  refine ⟨219273469598481392294443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74845344289614981903169877 219273469598481392294443)
                  ·
                    rfl

theorem cell22_1921651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_1921651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921651 prefixEnd_1921651 := by exact prefixLift 1921651
  have htrace : WordTrace (prefixWord ++ tailWord_1921651) baseStart_1921651 baseEnd_1921651 := by
    simpa [prefixWord, tailWord_1921651, baseEnd_1921651] using wordTrace_append hprefix tailTrace_1921651
  have hstable : (prefixWord ++ tailWord_1921651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921651).length < 2 ^ (prefixWord ++ tailWord_1921651).sum := by decide
  have hdescent : baseEnd_1921651 < baseStart_1921651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921661 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_1921661 : Nat := 118140960795 + 1921661 * 2 ^ 59
def prefixEnd_1921661 : Nat := 4983230072969 + 3 ^ 40 * 1921661 * 2
def baseEnd_1921661 : Nat := 657823831999807484133299

theorem tailTrace_1921661 : CollatzResearch.WordTrace tailWord_1921661 prefixEnd_1921661 657823831999807484133299 := by
  unfold tailWord_1921661
  simp only [CollatzResearch.WordTrace]
  refine ⟨70088734691157865415084837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46725823127438576943389891 70088734691157865415084837)
  ·
    refine ⟨13141637754592099765328407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70088734691157865415084837 13141637754592099765328407)
    ·
      refine ⟨19712456631888149647992611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13141637754592099765328407 19712456631888149647992611)
      ·
        refine ⟨29568684947832224471988917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19712456631888149647992611 29568684947832224471988917)
        ·
          refine ⟨2772064213859271044248961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29568684947832224471988917 2772064213859271044248961)
          ·
            refine ⟨2079048160394453283186721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772064213859271044248961 2079048160394453283186721)
            ·
              refine ⟨1559286120295839962390041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079048160394453283186721 1559286120295839962390041)
              ·
                refine ⟨1169464590221879971792531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559286120295839962390041 1169464590221879971792531)
                ·
                  refine ⟨1754196885332819957688797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169464590221879971792531 1754196885332819957688797)
                  ·
                    refine ⟨657823831999807484133299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754196885332819957688797 657823831999807484133299)
                    ·
                      rfl

theorem cell22_1921661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_1921661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921661 prefixEnd_1921661 := by exact prefixLift 1921661
  have htrace : WordTrace (prefixWord ++ tailWord_1921661) baseStart_1921661 baseEnd_1921661 := by
    simpa [prefixWord, tailWord_1921661, baseEnd_1921661] using wordTrace_append hprefix tailTrace_1921661
  have hstable : (prefixWord ++ tailWord_1921661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921661).length < 2 ^ (prefixWord ++ tailWord_1921661).sum := by decide
  have hdescent : baseEnd_1921661 < baseStart_1921661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921700 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1921700 : Nat := 118140960795 + 1921700 * 2 ^ 59
def prefixEnd_1921700 : Nat := 4983230072969 + 3 ^ 40 * 1921700 * 2
def baseEnd_1921700 : Nat := 657837182496824382408179

theorem tailTrace_1921700 : CollatzResearch.WordTrace tailWord_1921700 prefixEnd_1921700 657837182496824382408179 := by
  unfold tailWord_1921700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35045078569008287537877277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46726771425344383383836369 35045078569008287537877277)
  ·
    refine ⟨13141904463378107826703979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35045078569008287537877277 13141904463378107826703979)
    ·
      refine ⟨19712856695067161740055969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13141904463378107826703979 19712856695067161740055969)
      ·
        refine ⟨14784642521300371305041977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19712856695067161740055969 14784642521300371305041977)
        ·
          refine ⟨11088481890975278478781483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14784642521300371305041977 11088481890975278478781483)
          ·
            refine ⟨16632722836462917718172225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088481890975278478781483 16632722836462917718172225)
            ·
              refine ⟨12474542127347188288629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16632722836462917718172225 12474542127347188288629169)
              ·
                refine ⟨9355906595510391216471877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474542127347188288629169 9355906595510391216471877)
                ·
                  refine ⟨1754232486658198353088477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9355906595510391216471877 1754232486658198353088477)
                  ·
                    refine ⟨657837182496824382408179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754232486658198353088477 657837182496824382408179)
                    ·
                      rfl

theorem cell22_1921700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1921700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921700 prefixEnd_1921700 := by exact prefixLift 1921700
  have htrace : WordTrace (prefixWord ++ tailWord_1921700) baseStart_1921700 baseEnd_1921700 := by
    simpa [prefixWord, tailWord_1921700, baseEnd_1921700] using wordTrace_append hprefix tailTrace_1921700
  have hstable : (prefixWord ++ tailWord_1921700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921700).length < 2 ^ (prefixWord ++ tailWord_1921700).sum := by decide
  have hdescent : baseEnd_1921700 < baseStart_1921700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921717 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1921717 : Nat := 118140960795 + 1921717 * 2 ^ 59
def prefixEnd_1921717 : Nat := 4983230072969 + 3 ^ 40 * 1921717 * 2
def baseEnd_1921717 : Nat := 657843001944242004733127

theorem tailTrace_1921717 : CollatzResearch.WordTrace tailWord_1921717 prefixEnd_1921717 657843001944242004733127 := by
  unfold tailWord_1921717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70090777178954986979123405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46727184785969991319415603 70090777178954986979123405)
  ·
    refine ⟨26284041442108120117171277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70090777178954986979123405 26284041442108120117171277)
    ·
      refine ⟨9856515540790545043939229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26284041442108120117171277 9856515540790545043939229)
      ·
        refine ⟨3696193327796454391477211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9856515540790545043939229 3696193327796454391477211)
        ·
          refine ⟨5544289991694681587215817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696193327796454391477211 5544289991694681587215817)
          ·
            refine ⟨4158217493771011190411863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544289991694681587215817 4158217493771011190411863)
            ·
              refine ⟨6237326240656516785617795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158217493771011190411863 6237326240656516785617795)
              ·
                refine ⟨9355989360984775178426693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237326240656516785617795 9355989360984775178426693)
                ·
                  refine ⟨1754248005184645345955005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9355989360984775178426693 1754248005184645345955005)
                  ·
                    refine ⟨657843001944242004733127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754248005184645345955005 657843001944242004733127)
                    ·
                      rfl

theorem cell22_1921717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1921717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921717 prefixEnd_1921717 := by exact prefixLift 1921717
  have htrace : WordTrace (prefixWord ++ tailWord_1921717) baseStart_1921717 baseEnd_1921717 := by
    simpa [prefixWord, tailWord_1921717, baseEnd_1921717] using wordTrace_append hprefix tailTrace_1921717
  have hstable : (prefixWord ++ tailWord_1921717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921717).length < 2 ^ (prefixWord ++ tailWord_1921717).sum := by decide
  have hdescent : baseEnd_1921717 < baseStart_1921717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921745 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1921745 : Nat := 118140960795 + 1921745 * 2 ^ 59
def prefixEnd_1921745 : Nat := 4983230072969 + 3 ^ 40 * 1921745 * 2
def baseEnd_1921745 : Nat := 657852586916459265033041

theorem tailTrace_1921745 : CollatzResearch.WordTrace tailWord_1921745 prefixEnd_1921745 657852586916459265033041 := by
  unfold tailWord_1921745
  simp only [CollatzResearch.WordTrace]
  refine ⟨70091798422853547761142689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46727865615235698507428459 70091798422853547761142689)
  ·
    refine ⟨52568848817140160820857017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70091798422853547761142689 52568848817140160820857017)
    ·
      refine ⟨39426636612855120615642763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52568848817140160820857017 39426636612855120615642763)
      ·
        refine ⟨59139954919282680923464145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39426636612855120615642763 59139954919282680923464145)
        ·
          refine ⟨44354966189462010692598109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59139954919282680923464145 44354966189462010692598109)
          ·
            refine ⟨16633112321048254009724291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44354966189462010692598109 16633112321048254009724291)
            ·
              refine ⟨24949668481572381014586437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16633112321048254009724291 24949668481572381014586437)
              ·
                refine ⟨4678062840294821440234957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24949668481572381014586437 4678062840294821440234957)
                ·
                  refine ⟨1754273565110558040088109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4678062840294821440234957 1754273565110558040088109)
                  ·
                    refine ⟨657852586916459265033041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754273565110558040088109 657852586916459265033041)
                    ·
                      rfl

theorem cell22_1921745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1921745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921745 prefixEnd_1921745 := by exact prefixLift 1921745
  have htrace : WordTrace (prefixWord ++ tailWord_1921745) baseStart_1921745 baseEnd_1921745 := by
    simpa [prefixWord, tailWord_1921745, baseEnd_1921745] using wordTrace_append hprefix tailTrace_1921745
  have hstable : (prefixWord ++ tailWord_1921745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921745).length < 2 ^ (prefixWord ++ tailWord_1921745).sum := by decide
  have hdescent : baseEnd_1921745 < baseStart_1921745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921803 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 8]
def baseStart_1921803 : Nat := 118140960795 + 1921803 * 2 ^ 59
def prefixEnd_1921803 : Nat := 4983230072969 + 3 ^ 40 * 1921803 * 2
def baseEnd_1921803 : Nat := 219290813833922149027621

theorem tailTrace_1921803 : CollatzResearch.WordTrace tailWord_1921803 prefixEnd_1921803 219290813833922149027621 := by
  unfold tailWord_1921803
  simp only [CollatzResearch.WordTrace]
  refine ⟨70093913856643423666754063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46729275904428949111169375 70093913856643423666754063)
  ·
    refine ⟨105140870784965135500131095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70093913856643423666754063 105140870784965135500131095)
    ·
      refine ⟨157711306177447703250196643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105140870784965135500131095 157711306177447703250196643)
      ·
        refine ⟨236566959266171554875294965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157711306177447703250196643 236566959266171554875294965)
        ·
          refine ⟨22178152431203583269558903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236566959266171554875294965 22178152431203583269558903)
          ·
            refine ⟨33267228646805374904338355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22178152431203583269558903 33267228646805374904338355)
            ·
              refine ⟨49900842970208062356507533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33267228646805374904338355 49900842970208062356507533)
              ·
                refine ⟨18712816113828023383690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49900842970208062356507533 18712816113828023383690325)
                ·
                  refine ⟨219290813833922149027621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18712816113828023383690325 219290813833922149027621)
                  ·
                    rfl

theorem cell22_1921803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_1921803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921803 prefixEnd_1921803 := by exact prefixLift 1921803
  have htrace : WordTrace (prefixWord ++ tailWord_1921803) baseStart_1921803 baseEnd_1921803 := by
    simpa [prefixWord, tailWord_1921803, baseEnd_1921803] using wordTrace_append hprefix tailTrace_1921803
  have hstable : (prefixWord ++ tailWord_1921803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921803).length < 2 ^ (prefixWord ++ tailWord_1921803).sum := by decide
  have hdescent : baseEnd_1921803 < baseStart_1921803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921948 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_1921948 : Nat := 118140960795 + 1921948 * 2 ^ 59
def prefixEnd_1921948 : Nat := 4983230072969 + 3 ^ 40 * 1921948 * 2
def baseEnd_1921948 : Nat := 657922077965034402207419

theorem tailTrace_1921948 : CollatzResearch.WordTrace tailWord_1921948 prefixEnd_1921948 657922077965034402207419 := by
  unfold tailWord_1921948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35049601220559056715391249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46732801627412075620521665 35049601220559056715391249)
  ·
    refine ⟨26287200915419292536543437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35049601220559056715391249 26287200915419292536543437)
    ·
      refine ⟨9857700343282234701203789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26287200915419292536543437 9857700343282234701203789)
      ·
        refine ⟨3696637628730838012951421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9857700343282234701203789 3696637628730838012951421)
        ·
          refine ⟨1386239110774064254856783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3696637628730838012951421 1386239110774064254856783)
          ·
            refine ⟨2079358666161096382285175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386239110774064254856783 2079358666161096382285175)
            ·
              refine ⟨3119037999241644573427763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079358666161096382285175 3119037999241644573427763)
              ·
                refine ⟨4678556998862466860141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119037999241644573427763 4678556998862466860141645)
                ·
                  refine ⟨1754458874573425072553117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4678556998862466860141645 1754458874573425072553117)
                  ·
                    refine ⟨657922077965034402207419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754458874573425072553117 657922077965034402207419)
                    ·
                      rfl

theorem cell22_1921948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_1921948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1921948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1921948 prefixEnd_1921948 := by exact prefixLift 1921948
  have htrace : WordTrace (prefixWord ++ tailWord_1921948) baseStart_1921948 baseEnd_1921948 := by
    simpa [prefixWord, tailWord_1921948, baseEnd_1921948] using wordTrace_append hprefix tailTrace_1921948
  have hstable : (prefixWord ++ tailWord_1921948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921948).length < 2 ^ (prefixWord ++ tailWord_1921948).sum := by decide
  have hdescent : baseEnd_1921948 < baseStart_1921948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922021 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1922021 : Nat := 118140960795 + 1922021 * 2 ^ 59
def prefixEnd_1922021 : Nat := 4983230072969 + 3 ^ 40 * 1922021 * 2
def baseEnd_1922021 : Nat := 657947067356886545132195

theorem tailTrace_1922021 : CollatzResearch.WordTrace tailWord_1922021 prefixEnd_1922021 657947067356886545132195 := by
  unfold tailWord_1922021
  simp only [CollatzResearch.WordTrace]
  refine ⟨70101864969853646898189917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46734576646569097932126611 70101864969853646898189917)
  ·
    refine ⟨26288199363695117586821219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70101864969853646898189917 26288199363695117586821219)
    ·
      refine ⟨39432299045542676380231829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26288199363695117586821219 39432299045542676380231829)
      ·
        refine ⟨1848389017759812955323367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39432299045542676380231829 1848389017759812955323367)
        ·
          refine ⟨2772583526639719432985051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848389017759812955323367 2772583526639719432985051)
          ·
            refine ⟨4158875289959579149477577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772583526639719432985051 4158875289959579149477577)
            ·
              refine ⟨3119156467469684362108183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158875289959579149477577 3119156467469684362108183)
              ·
                refine ⟨4678734701204526543162275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119156467469684362108183 4678734701204526543162275)
                ·
                  refine ⟨7018102051806789814743413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678734701204526543162275 7018102051806789814743413)
                  ·
                    refine ⟨657947067356886545132195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7018102051806789814743413 657947067356886545132195)
                    ·
                      rfl

theorem cell22_1922021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1922021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922021 prefixEnd_1922021 := by exact prefixLift 1922021
  have htrace : WordTrace (prefixWord ++ tailWord_1922021) baseStart_1922021 baseEnd_1922021 := by
    simpa [prefixWord, tailWord_1922021, baseEnd_1922021] using wordTrace_append hprefix tailTrace_1922021
  have hstable : (prefixWord ++ tailWord_1922021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922021).length < 2 ^ (prefixWord ++ tailWord_1922021).sum := by decide
  have hdescent : baseEnd_1922021 < baseStart_1922021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922100 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1922100 : Nat := 118140960795 + 1922100 * 2 ^ 59
def prefixEnd_1922100 : Nat := 4983230072969 + 3 ^ 40 * 1922100 * 2
def baseEnd_1922100 : Nat := 657974110671356672406953

theorem tailTrace_1922100 : CollatzResearch.WordTrace tailWord_1922100 prefixEnd_1922100 657974110671356672406953 := by
  unfold tailWord_1922100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052373168283721695157877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46736497557711628926877169 35052373168283721695157877)
  ·
    refine ⟨3286159984526598908921051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35052373168283721695157877 3286159984526598908921051)
    ·
      refine ⟨4929239976789898363381577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286159984526598908921051 4929239976789898363381577)
      ·
        refine ⟨3696929982592423772536183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929239976789898363381577 3696929982592423772536183)
        ·
          refine ⟨5545394973888635658804275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696929982592423772536183 5545394973888635658804275)
          ·
            refine ⟨8318092460832953488206413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545394973888635658804275 8318092460832953488206413)
            ·
              refine ⟨3119284672812357558077405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8318092460832953488206413 3119284672812357558077405)
              ·
                refine ⟨1169731752304634084279027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3119284672812357558077405 1169731752304634084279027)
                ·
                  refine ⟨1754597628456951126418541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169731752304634084279027 1754597628456951126418541)
                  ·
                    refine ⟨657974110671356672406953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754597628456951126418541 657974110671356672406953)
                    ·
                      rfl

theorem cell22_1922100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1922100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922100 prefixEnd_1922100 := by exact prefixLift 1922100
  have htrace : WordTrace (prefixWord ++ tailWord_1922100) baseStart_1922100 baseEnd_1922100 := by
    simpa [prefixWord, tailWord_1922100, baseEnd_1922100] using wordTrace_append hprefix tailTrace_1922100
  have hstable : (prefixWord ++ tailWord_1922100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922100).length < 2 ^ (prefixWord ++ tailWord_1922100).sum := by decide
  have hdescent : baseEnd_1922100 < baseStart_1922100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922137 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1922137 : Nat := 118140960795 + 1922137 * 2 ^ 59
def prefixEnd_1922137 : Nat := 4983230072969 + 3 ^ 40 * 1922137 * 2
def baseEnd_1922137 : Nat := 657986776527500909231839

theorem tailTrace_1922137 : CollatzResearch.WordTrace tailWord_1922137 prefixEnd_1922137 657986776527500909231839 := by
  unfold tailWord_1922137
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106095837433398709412665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46737397224955599139608443 70106095837433398709412665)
  ·
    refine ⟨52579571878075049032059499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70106095837433398709412665 52579571878075049032059499)
    ·
      refine ⟨78869357817112573548089249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52579571878075049032059499 78869357817112573548089249)
      ·
        refine ⟨59152018362834430161066937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78869357817112573548089249 59152018362834430161066937)
        ·
          refine ⟨44364013772125822620800203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59152018362834430161066937 44364013772125822620800203)
          ·
            refine ⟨66546020658188733931200305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44364013772125822620800203 66546020658188733931200305)
            ·
              refine ⟨49909515493641550448400229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66546020658188733931200305 49909515493641550448400229)
              ·
                refine ⟨9358034155057790709075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49909515493641550448400229 9358034155057790709075043)
                ·
                  refine ⟨14037051232586686063612565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358034155057790709075043 14037051232586686063612565)
                  ·
                    refine ⟨657986776527500909231839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14037051232586686063612565 657986776527500909231839)
                    ·
                      rfl

theorem cell22_1922137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1922137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922137 prefixEnd_1922137 := by exact prefixLift 1922137
  have htrace : WordTrace (prefixWord ++ tailWord_1922137) baseStart_1922137 baseEnd_1922137 := by
    simpa [prefixWord, tailWord_1922137, baseEnd_1922137] using wordTrace_append hprefix tailTrace_1922137
  have hstable : (prefixWord ++ tailWord_1922137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922137).length < 2 ^ (prefixWord ++ tailWord_1922137).sum := by decide
  have hdescent : baseEnd_1922137 < baseStart_1922137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922169 : List Nat := [1, 2, 1, 3, 6, 9]
def baseStart_1922169 : Nat := 118140960795 + 1922169 * 2 ^ 59
def prefixEnd_1922169 : Nat := 4983230072969 + 3 ^ 40 * 1922169 * 2
def baseEnd_1922169 : Nat := 8123428775079796202861

theorem tailTrace_1922169 : CollatzResearch.WordTrace tailWord_1922169 prefixEnd_1922169 8123428775079796202861 := by
  unfold tailWord_1922169
  simp only [CollatzResearch.WordTrace]
  refine ⟨70107262973317468174577561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46738175315544978783051707 70107262973317468174577561)
  ·
    refine ⟨52580447229988101130933171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70107262973317468174577561 52580447229988101130933171)
    ·
      refine ⟨78870670844982151696399757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52580447229988101130933171 78870670844982151696399757)
      ·
        refine ⟨29576501566868306886149909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78870670844982151696399757 29576501566868306886149909)
        ·
          refine ⟨1386398510946951885288277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29576501566868306886149909 1386398510946951885288277)
          ·
            refine ⟨8123428775079796202861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1386398510946951885288277 8123428775079796202861)
            ·
              rfl

theorem cell22_1922169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 9].length) (baseStart_1922169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922169 prefixEnd_1922169 := by exact prefixLift 1922169
  have htrace : WordTrace (prefixWord ++ tailWord_1922169) baseStart_1922169 baseEnd_1922169 := by
    simpa [prefixWord, tailWord_1922169, baseEnd_1922169] using wordTrace_append hprefix tailTrace_1922169
  have hstable : (prefixWord ++ tailWord_1922169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922169).length < 2 ^ (prefixWord ++ tailWord_1922169).sum := by decide
  have hdescent : baseEnd_1922169 < baseStart_1922169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922269 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1922269 : Nat := 118140960795 + 1922269 * 2 ^ 59
def prefixEnd_1922269 : Nat := 4983230072969 + 3 ^ 40 * 1922269 * 2
def baseEnd_1922269 : Nat := 658031962825096564931435

theorem tailTrace_1922269 : CollatzResearch.WordTrace tailWord_1922269 prefixEnd_1922269 658031962825096564931435 := by
  unfold tailWord_1922269
  simp only [CollatzResearch.WordTrace]
  refine ⟨70110910272955185253217861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46740606848636790168811907 70110910272955185253217861)
  ·
    refine ⟨13145795676179097234978349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70110910272955185253217861 13145795676179097234978349)
    ·
      refine ⟨4929673378567161463116881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13145795676179097234978349 4929673378567161463116881)
      ·
        refine ⟨3697255033925371097337661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929673378567161463116881 3697255033925371097337661)
        ·
          refine ⟨1386470637722014161501623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697255033925371097337661 1386470637722014161501623)
          ·
            refine ⟨2079705956583021242252435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386470637722014161501623 2079705956583021242252435)
            ·
              refine ⟨3119558934874531863378653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079705956583021242252435 3119558934874531863378653)
              ·
                refine ⟨1169834600577949448766995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3119558934874531863378653 1169834600577949448766995)
                ·
                  refine ⟨1754751900866924173150493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169834600577949448766995 1754751900866924173150493)
                  ·
                    refine ⟨658031962825096564931435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754751900866924173150493 658031962825096564931435)
                    ·
                      rfl

theorem cell22_1922269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1922269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922269 prefixEnd_1922269 := by exact prefixLift 1922269
  have htrace : WordTrace (prefixWord ++ tailWord_1922269) baseStart_1922269 baseEnd_1922269 := by
    simpa [prefixWord, tailWord_1922269, baseEnd_1922269] using wordTrace_append hprefix tailTrace_1922269
  have hstable : (prefixWord ++ tailWord_1922269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922269).length < 2 ^ (prefixWord ++ tailWord_1922269).sum := by decide
  have hdescent : baseEnd_1922269 < baseStart_1922269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922291 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 4, 3]
def baseStart_1922291 : Nat := 118140960795 + 1922291 * 2 ^ 59
def prefixEnd_1922291 : Nat := 4983230072969 + 3 ^ 40 * 1922291 * 2
def baseEnd_1922291 : Nat := 658039493874695840881367

theorem tailTrace_1922291 : CollatzResearch.WordTrace tailWord_1922291 prefixEnd_1922291 658039493874695840881367 := by
  unfold tailWord_1922291
  simp only [CollatzResearch.WordTrace]
  refine ⟨70111712678875483010518727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46741141785916988673679151 70111712678875483010518727)
  ·
    refine ⟨105167569018313224515778091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70111712678875483010518727 105167569018313224515778091)
    ·
      refine ⟨157751353527469836773667137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105167569018313224515778091 157751353527469836773667137)
      ·
        refine ⟨118313515145602377580250353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157751353527469836773667137 118313515145602377580250353)
        ·
          refine ⟨88735136359201783185187765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118313515145602377580250353 88735136359201783185187765)
          ·
            refine ⟨8318919033675167173611353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88735136359201783185187765 8318919033675167173611353)
            ·
              refine ⟨6239189275256375380208515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318919033675167173611353 6239189275256375380208515)
              ·
                refine ⟨9358783912884563070312773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239189275256375380208515 9358783912884563070312773)
                ·
                  refine ⟨1754771983665855575683645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9358783912884563070312773 1754771983665855575683645)
                  ·
                    refine ⟨658039493874695840881367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754771983665855575683645 658039493874695840881367)
                    ·
                      rfl

theorem cell22_1922291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].length) (baseStart_1922291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922291 prefixEnd_1922291 := by exact prefixLift 1922291
  have htrace : WordTrace (prefixWord ++ tailWord_1922291) baseStart_1922291 baseEnd_1922291 := by
    simpa [prefixWord, tailWord_1922291, baseEnd_1922291] using wordTrace_append hprefix tailTrace_1922291
  have hstable : (prefixWord ++ tailWord_1922291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922291).length < 2 ^ (prefixWord ++ tailWord_1922291).sum := by decide
  have hdescent : baseEnd_1922291 < baseStart_1922291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922374 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1922374 : Nat := 118140960795 + 1922374 * 2 ^ 59
def prefixEnd_1922374 : Nat := 4983230072969 + 3 ^ 40 * 1922374 * 2
def baseEnd_1922374 : Nat := 658067906470911291056113

theorem tailTrace_1922374 : CollatzResearch.WordTrace tailWord_1922374 prefixEnd_1922374 658067906470911291056113 := by
  unfold tailWord_1922374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191085623049212130805943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46743159958383192123860117 2191085623049212130805943)
  ·
    refine ⟨3286628434573818196208915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191085623049212130805943 3286628434573818196208915)
    ·
      refine ⟨4929942651860727294313373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286628434573818196208915 4929942651860727294313373)
      ·
        refine ⟨1848728494447772735367515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4929942651860727294313373 1848728494447772735367515)
        ·
          refine ⟨2773092741671659103051273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848728494447772735367515 2773092741671659103051273)
          ·
            refine ⟨2079819556253744327288455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773092741671659103051273 2079819556253744327288455)
            ·
              refine ⟨3119729334380616490932683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079819556253744327288455 3119729334380616490932683)
              ·
                refine ⟨4679594001570924736399025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119729334380616490932683 4679594001570924736399025)
                ·
                  refine ⟨3509695501178193552299269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679594001570924736399025 3509695501178193552299269)
                  ·
                    refine ⟨658067906470911291056113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509695501178193552299269 658067906470911291056113)
                    ·
                      rfl

theorem cell22_1922374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1922374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922374 prefixEnd_1922374 := by exact prefixLift 1922374
  have htrace : WordTrace (prefixWord ++ tailWord_1922374) baseStart_1922374 baseEnd_1922374 := by
    simpa [prefixWord, tailWord_1922374, baseEnd_1922374] using wordTrace_append hprefix tailTrace_1922374
  have hstable : (prefixWord ++ tailWord_1922374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922374).length < 2 ^ (prefixWord ++ tailWord_1922374).sum := by decide
  have hdescent : baseEnd_1922374 < baseStart_1922374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922458 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1922458 : Nat := 118140960795 + 1922458 * 2 ^ 59
def prefixEnd_1922458 : Nat := 4983230072969 + 3 ^ 40 * 1922458 * 2
def baseEnd_1922458 : Nat := 658096661387563071955855

theorem tailTrace_1922458 : CollatzResearch.WordTrace tailWord_1922458 prefixEnd_1922458 658096661387563071955855 := by
  unfold tailWord_1922458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529450917317617632962007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46745202446180313687898685 17529450917317617632962007)
  ·
    refine ⟨26294176375976426449443011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17529450917317617632962007 26294176375976426449443011)
    ·
      refine ⟨39441264563964639674164517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26294176375976426449443011 39441264563964639674164517)
      ·
        refine ⟨7395237105743369938905847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39441264563964639674164517 7395237105743369938905847)
        ·
          refine ⟨11092855658615054908358771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395237105743369938905847 11092855658615054908358771)
          ·
            refine ⟨16639283487922582362538157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092855658615054908358771 16639283487922582362538157)
            ·
              refine ⟨6239731307970968385951809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16639283487922582362538157 6239731307970968385951809)
              ·
                refine ⟨4679798480978226289463857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239731307970968385951809 4679798480978226289463857)
                ·
                  refine ⟨3509848860733669717097893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679798480978226289463857 3509848860733669717097893)
                  ·
                    refine ⟨658096661387563071955855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509848860733669717097893 658096661387563071955855)
                    ·
                      rfl

theorem cell22_1922458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1922458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922458 prefixEnd_1922458 := by exact prefixLift 1922458
  have htrace : WordTrace (prefixWord ++ tailWord_1922458) baseStart_1922458 baseEnd_1922458 := by
    simpa [prefixWord, tailWord_1922458, baseEnd_1922458] using wordTrace_append hprefix tailTrace_1922458
  have hstable : (prefixWord ++ tailWord_1922458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922458).length < 2 ^ (prefixWord ++ tailWord_1922458).sum := by decide
  have hdescent : baseEnd_1922458 < baseStart_1922458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922462 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1922462 : Nat := 118140960795 + 1922462 * 2 ^ 59
def prefixEnd_1922462 : Nat := 4983230072969 + 3 ^ 40 * 1922462 * 2
def baseEnd_1922462 : Nat := 219366010223102798285281

theorem tailTrace_1922462 : CollatzResearch.WordTrace tailWord_1922462 prefixEnd_1922462 219366010223102798285281 := by
  unfold tailWord_1922462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764743695156997401874205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46745299707503986143329093 8764743695156997401874205)
  ·
    refine ⟨3286778885683874025702827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8764743695156997401874205 3286778885683874025702827)
    ·
      refine ⟨4930168328525811038554241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286778885683874025702827 4930168328525811038554241)
      ·
        refine ⟨3697626246394358278915681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930168328525811038554241 3697626246394358278915681)
        ·
          refine ⟨2773219684795768709186761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697626246394358278915681 2773219684795768709186761)
          ·
            refine ⟨2079914763596826531890071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773219684795768709186761 2079914763596826531890071)
            ·
              refine ⟨3119872145395239797835107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079914763596826531890071 3119872145395239797835107)
              ·
                refine ⟨4679808218092859696752661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119872145395239797835107 4679808218092859696752661)
                ·
                  refine ⟨219366010223102798285281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4679808218092859696752661 219366010223102798285281)
                  ·
                    rfl

theorem cell22_1922462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1922462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922462 prefixEnd_1922462 := by exact prefixLift 1922462
  have htrace : WordTrace (prefixWord ++ tailWord_1922462) baseStart_1922462 baseEnd_1922462 := by
    simpa [prefixWord, tailWord_1922462, baseEnd_1922462] using wordTrace_append hprefix tailTrace_1922462
  have hstable : (prefixWord ++ tailWord_1922462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922462).length < 2 ^ (prefixWord ++ tailWord_1922462).sum := by decide
  have hdescent : baseEnd_1922462 < baseStart_1922462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922477 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1922477 : Nat := 118140960795 + 1922477 * 2 ^ 59
def prefixEnd_1922477 : Nat := 4983230072969 + 3 ^ 40 * 1922477 * 2
def baseEnd_1922477 : Nat := 658103165475853355730797

theorem tailTrace_1922477 : CollatzResearch.WordTrace tailWord_1922477 prefixEnd_1922477 658103165475853355730797 := by
  unfold tailWord_1922477
  simp only [CollatzResearch.WordTrace]
  refine ⟨70118496656201636776789685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46745664437467757851193123 70118496656201636776789685)
  ·
    refine ⟨6573609061518903447824033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70118496656201636776789685 6573609061518903447824033)
    ·
      refine ⟨4930206796139177585868025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6573609061518903447824033 4930206796139177585868025)
      ·
        refine ⟨3697655097104383189401019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930206796139177585868025 3697655097104383189401019)
        ·
          refine ⟨5546482645656574784101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697655097104383189401019 5546482645656574784101529)
          ·
            refine ⟨4159861984242431088076147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546482645656574784101529 4159861984242431088076147)
            ·
              refine ⟨6239792976363646632114221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159861984242431088076147 6239792976363646632114221)
              ·
                refine ⟨2339922366136367487042833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6239792976363646632114221 2339922366136367487042833)
                ·
                  refine ⟨1754941774602275615282125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2339922366136367487042833 1754941774602275615282125)
                  ·
                    refine ⟨658103165475853355730797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754941774602275615282125 658103165475853355730797)
                    ·
                      rfl

theorem cell22_1922477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1922477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922477 prefixEnd_1922477 := by exact prefixLift 1922477
  have htrace : WordTrace (prefixWord ++ tailWord_1922477) baseStart_1922477 baseEnd_1922477 := by
    simpa [prefixWord, tailWord_1922477, baseEnd_1922477] using wordTrace_append hprefix tailTrace_1922477
  have hstable : (prefixWord ++ tailWord_1922477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922477).length < 2 ^ (prefixWord ++ tailWord_1922477).sum := by decide
  have hdescent : baseEnd_1922477 < baseStart_1922477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922488 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_1922488 : Nat := 118140960795 + 1922488 * 2 ^ 59
def prefixEnd_1922488 : Nat := 4983230072969 + 3 ^ 40 * 1922488 * 2
def baseEnd_1922488 : Nat := 658106931000652993705763

theorem tailTrace_1922488 : CollatzResearch.WordTrace tailWord_1922488 prefixEnd_1922488 658106931000652993705763 := by
  unfold tailWord_1922488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35059448929580892827720059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46745931906107857103626745 35059448929580892827720059)
  ·
    refine ⟨52589173394371339241580089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35059448929580892827720059 52589173394371339241580089)
    ·
      refine ⟨39441880045778504431185067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52589173394371339241580089 39441880045778504431185067)
      ·
        refine ⟨59162820068667756646777601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39441880045778504431185067 59162820068667756646777601)
        ·
          refine ⟨44372115051500817485083201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59162820068667756646777601 44372115051500817485083201)
          ·
            refine ⟨33279086288625613113812401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44372115051500817485083201 33279086288625613113812401)
            ·
              refine ⟨24959314716469209835359301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33279086288625613113812401 24959314716469209835359301)
              ·
                refine ⟨4679871509337976844129869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24959314716469209835359301 4679871509337976844129869)
                ·
                  refine ⟨1754951816001741316548701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4679871509337976844129869 1754951816001741316548701)
                  ·
                    refine ⟨658106931000652993705763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754951816001741316548701 658106931000652993705763)
                    ·
                      rfl

theorem cell22_1922488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_1922488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922488 prefixEnd_1922488 := by exact prefixLift 1922488
  have htrace : WordTrace (prefixWord ++ tailWord_1922488) baseStart_1922488 baseEnd_1922488 := by
    simpa [prefixWord, tailWord_1922488, baseEnd_1922488] using wordTrace_append hprefix tailTrace_1922488
  have hstable : (prefixWord ++ tailWord_1922488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922488).length < 2 ^ (prefixWord ++ tailWord_1922488).sum := by decide
  have hdescent : baseEnd_1922488 < baseStart_1922488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922498 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1922498 : Nat := 118140960795 + 1922498 * 2 ^ 59
def prefixEnd_1922498 : Nat := 4983230072969 + 3 ^ 40 * 1922498 * 2
def baseEnd_1922498 : Nat := 658110354205016300955733

theorem tailTrace_1922498 : CollatzResearch.WordTrace tailWord_1922498 prefixEnd_1922498 658110354205016300955733 := by
  unfold tailWord_1922498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529815647281389340826037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46746175059417038242202765 17529815647281389340826037)
  ·
    refine ⟨1643420216932630250702441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17529815647281389340826037 1643420216932630250702441)
    ·
      refine ⟨1232565162699472688026831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1643420216932630250702441 1232565162699472688026831)
      ·
        refine ⟨1848847744049209032040247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232565162699472688026831 1848847744049209032040247)
        ·
          refine ⟨2773271616073813548060371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848847744049209032040247 2773271616073813548060371)
          ·
            refine ⟨4159907424110720322090557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773271616073813548060371 4159907424110720322090557)
            ·
              refine ⟨1559965284041520120783959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4159907424110720322090557 1559965284041520120783959)
              ·
                refine ⟨2339947926062280181175939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559965284041520120783959 2339947926062280181175939)
                ·
                  refine ⟨3509921889093420271763909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339947926062280181175939 3509921889093420271763909)
                  ·
                    refine ⟨658110354205016300955733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509921889093420271763909 658110354205016300955733)
                    ·
                      rfl

theorem cell22_1922498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1922498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922498 prefixEnd_1922498 := by exact prefixLift 1922498
  have htrace : WordTrace (prefixWord ++ tailWord_1922498) baseStart_1922498 baseEnd_1922498 := by
    simpa [prefixWord, tailWord_1922498, baseEnd_1922498] using wordTrace_append hprefix tailTrace_1922498
  have hstable : (prefixWord ++ tailWord_1922498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922498).length < 2 ^ (prefixWord ++ tailWord_1922498).sum := by decide
  have hdescent : baseEnd_1922498 < baseStart_1922498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922505 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_1922505 : Nat := 118140960795 + 1922505 * 2 ^ 59
def prefixEnd_1922505 : Nat := 4983230072969 + 3 ^ 40 * 1922505 * 2
def baseEnd_1922505 : Nat := 658112750448070616030711

theorem tailTrace_1922505 : CollatzResearch.WordTrace tailWord_1922505 prefixEnd_1922505 658112750448070616030711 := by
  unfold tailWord_1922505
  simp only [CollatzResearch.WordTrace]
  refine ⟨70119517900100197558808969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46746345266733465039205979 70119517900100197558808969)
  ·
    refine ⟨52589638425075148169106727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70119517900100197558808969 52589638425075148169106727)
    ·
      refine ⟨78884457637612722253660091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52589638425075148169106727 78884457637612722253660091)
      ·
        refine ⟨118326686456419083380490137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78884457637612722253660091 118326686456419083380490137)
        ·
          refine ⟨88745014842314312535367603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118326686456419083380490137 88745014842314312535367603)
          ·
            refine ⟨133117522263471468803051405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88745014842314312535367603 133117522263471468803051405)
            ·
              refine ⟨49919070848801800801144277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133117522263471468803051405 49919070848801800801144277)
              ·
                refine ⟨1169978223018792206276819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49919070848801800801144277 1169978223018792206276819)
                ·
                  refine ⟨1754967334528188309415229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169978223018792206276819 1754967334528188309415229)
                  ·
                    refine ⟨658112750448070616030711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754967334528188309415229 658112750448070616030711)
                    ·
                      rfl

theorem cell22_1922505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_1922505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922505 prefixEnd_1922505 := by exact prefixLift 1922505
  have htrace : WordTrace (prefixWord ++ tailWord_1922505) baseStart_1922505 baseEnd_1922505 := by
    simpa [prefixWord, tailWord_1922505, baseEnd_1922505] using wordTrace_append hprefix tailTrace_1922505
  have hstable : (prefixWord ++ tailWord_1922505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922505).length < 2 ^ (prefixWord ++ tailWord_1922505).sum := by decide
  have hdescent : baseEnd_1922505 < baseStart_1922505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922522 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_1922522 : Nat := 118140960795 + 1922522 * 2 ^ 59
def prefixEnd_1922522 : Nat := 4983230072969 + 3 ^ 40 * 1922522 * 2
def baseEnd_1922522 : Nat := 658118569895488238355659

theorem tailTrace_1922522 : CollatzResearch.WordTrace tailWord_1922522 prefixEnd_1922522 658118569895488238355659 := by
  unfold tailWord_1922522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530034485259652365544455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46746758627359072974785213 17530034485259652365544455)
  ·
    refine ⟨26295051727889478548316683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530034485259652365544455 26295051727889478548316683)
    ·
      refine ⟨39442577591834217822475025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295051727889478548316683 39442577591834217822475025)
      ·
        refine ⟨29581933193875663366856269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39442577591834217822475025 29581933193875663366856269)
        ·
          refine ⟨11093224947703373762571101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29581933193875663366856269 11093224947703373762571101)
          ·
            refine ⟨4159959355388765160964163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11093224947703373762571101 4159959355388765160964163)
            ·
              refine ⟨6239939033083147741446245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159959355388765160964163 6239939033083147741446245)
              ·
                refine ⟨1169988568703090201521171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6239939033083147741446245 1169988568703090201521171)
                ·
                  refine ⟨1754982853054635302281757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169988568703090201521171 1754982853054635302281757)
                  ·
                    refine ⟨658118569895488238355659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1754982853054635302281757 658118569895488238355659)
                    ·
                      rfl

theorem cell22_1922522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_1922522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922522 prefixEnd_1922522 := by exact prefixLift 1922522
  have htrace : WordTrace (prefixWord ++ tailWord_1922522) baseStart_1922522 baseEnd_1922522 := by
    simpa [prefixWord, tailWord_1922522, baseEnd_1922522] using wordTrace_append hprefix tailTrace_1922522
  have hstable : (prefixWord ++ tailWord_1922522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922522).length < 2 ^ (prefixWord ++ tailWord_1922522).sum := by decide
  have hdescent : baseEnd_1922522 < baseStart_1922522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922533 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1922533 : Nat := 118140960795 + 1922533 * 2 ^ 59
def prefixEnd_1922533 : Nat := 4983230072969 + 3 ^ 40 * 1922533 * 2
def baseEnd_1922533 : Nat := 658122335420287876330625

theorem tailTrace_1922533 : CollatzResearch.WordTrace tailWord_1922533 prefixEnd_1922533 658122335420287876330625 := by
  unfold tailWord_1922533
  simp only [CollatzResearch.WordTrace]
  refine ⟨70120539143998758340828253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46747026095999172227218835 70120539143998758340828253)
  ·
    refine ⟨26295202178999534377810595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70120539143998758340828253 26295202178999534377810595)
    ·
      refine ⟨39442803268499301566715893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295202178999534377810595 39442803268499301566715893)
      ·
        refine ⟨3697762806421809521879615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39442803268499301566715893 3697762806421809521879615)
        ·
          refine ⟨5546644209632714282819423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697762806421809521879615 5546644209632714282819423)
          ·
            refine ⟨8319966314449071424229135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546644209632714282819423 8319966314449071424229135)
            ·
              refine ⟨12479949471673607136343703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319966314449071424229135 12479949471673607136343703)
              ·
                refine ⟨18719924207510410704515555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479949471673607136343703 18719924207510410704515555)
                ·
                  refine ⟨28079886311265616056773333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18719924207510410704515555 28079886311265616056773333)
                  ·
                    refine ⟨658122335420287876330625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28079886311265616056773333 658122335420287876330625)
                    ·
                      rfl

theorem cell22_1922533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1922533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922533 prefixEnd_1922533 := by exact prefixLift 1922533
  have htrace : WordTrace (prefixWord ++ tailWord_1922533) baseStart_1922533 baseEnd_1922533 := by
    simpa [prefixWord, tailWord_1922533, baseEnd_1922533] using wordTrace_append hprefix tailTrace_1922533
  have hstable : (prefixWord ++ tailWord_1922533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922533).length < 2 ^ (prefixWord ++ tailWord_1922533).sum := by decide
  have hdescent : baseEnd_1922533 < baseStart_1922533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922593 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1922593 : Nat := 118140960795 + 1922593 * 2 ^ 59
def prefixEnd_1922593 : Nat := 4983230072969 + 3 ^ 40 * 1922593 * 2
def baseEnd_1922593 : Nat := 658142874646467719830441

theorem tailTrace_1922593 : CollatzResearch.WordTrace tailWord_1922593 prefixEnd_1922593 658142874646467719830441 := by
  unfold tailWord_1922593
  simp only [CollatzResearch.WordTrace]
  refine ⟨70122727523781388588012433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46748485015854259058674955 70122727523781388588012433)
  ·
    refine ⟨52592045642836041441009325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70122727523781388588012433 52592045642836041441009325)
    ·
      refine ⟨19722017116063515540378497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52592045642836041441009325 19722017116063515540378497)
      ·
        refine ⟨14791512837047636655283873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19722017116063515540378497 14791512837047636655283873)
        ·
          refine ⟨11093634627785727491462905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14791512837047636655283873 11093634627785727491462905)
          ·
            refine ⟨8320225970839295618597179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093634627785727491462905 8320225970839295618597179)
            ·
              refine ⟨12480338956258943427895769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320225970839295618597179 12480338956258943427895769)
              ·
                refine ⟨9360254217194207570921827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12480338956258943427895769 9360254217194207570921827)
                ·
                  refine ⟨14040381325791311356382741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9360254217194207570921827 14040381325791311356382741)
                  ·
                    refine ⟨658142874646467719830441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14040381325791311356382741 658142874646467719830441)
                    ·
                      rfl

theorem cell22_1922593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1922593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922593 prefixEnd_1922593 := by exact prefixLift 1922593
  have htrace : WordTrace (prefixWord ++ tailWord_1922593) baseStart_1922593 baseEnd_1922593 := by
    simpa [prefixWord, tailWord_1922593, baseEnd_1922593] using wordTrace_append hprefix tailTrace_1922593
  have hstable : (prefixWord ++ tailWord_1922593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922593).length < 2 ^ (prefixWord ++ tailWord_1922593).sum := by decide
  have hdescent : baseEnd_1922593 < baseStart_1922593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922638 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1922638 : Nat := 118140960795 + 1922638 * 2 ^ 59
def prefixEnd_1922638 : Nat := 4983230072969 + 3 ^ 40 * 1922638 * 2
def baseEnd_1922638 : Nat := 658158279066102602455303

theorem tailTrace_1922638 : CollatzResearch.WordTrace tailWord_1922638 prefixEnd_1922638 658158279066102602455303 := by
  unfold tailWord_1922638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765546101077295159175071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46749579205745574182267045 8765546101077295159175071)
  ·
    refine ⟨13148319151615942738762607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765546101077295159175071 13148319151615942738762607)
    ·
      refine ⟨19722478727423914108143911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148319151615942738762607 19722478727423914108143911)
      ·
        refine ⟨29583718091135871162215867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722478727423914108143911 29583718091135871162215867)
        ·
          refine ⟨44375577136703806743323801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29583718091135871162215867 44375577136703806743323801)
          ·
            refine ⟨33281682852527855057492851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44375577136703806743323801 33281682852527855057492851)
            ·
              refine ⟨49922524278791782586239277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33281682852527855057492851 49922524278791782586239277)
              ·
                refine ⟨18720946604546918469839729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49922524278791782586239277 18720946604546918469839729)
                ·
                  refine ⟨14040709953410188852379797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18720946604546918469839729 14040709953410188852379797)
                  ·
                    refine ⟨658158279066102602455303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14040709953410188852379797 658158279066102602455303)
                    ·
                      rfl

theorem cell22_1922638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1922638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922638 prefixEnd_1922638 := by exact prefixLift 1922638
  have htrace : WordTrace (prefixWord ++ tailWord_1922638) baseStart_1922638 baseEnd_1922638 := by
    simpa [prefixWord, tailWord_1922638, baseEnd_1922638] using wordTrace_append hprefix tailTrace_1922638
  have hstable : (prefixWord ++ tailWord_1922638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922638).length < 2 ^ (prefixWord ++ tailWord_1922638).sum := by decide
  have hdescent : baseEnd_1922638 < baseStart_1922638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922668 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1922668 : Nat := 118140960795 + 1922668 * 2 ^ 59
def prefixEnd_1922668 : Nat := 4983230072969 + 3 ^ 40 * 1922668 * 2
def baseEnd_1922668 : Nat := 658168548679192524205211

theorem tailTrace_1922668 : CollatzResearch.WordTrace tailWord_1922668 prefixEnd_1922668 658168548679192524205211 := by
  unfold tailWord_1922668
  simp only [CollatzResearch.WordTrace]
  refine ⟨35062731499254838198496329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46750308665673117597995105 35062731499254838198496329)
  ·
    refine ⟨26297048624441128648872247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35062731499254838198496329 26297048624441128648872247)
    ·
      refine ⟨39445572936661692973308371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26297048624441128648872247 39445572936661692973308371)
      ·
        refine ⟨59168359404992539459962557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39445572936661692973308371 59168359404992539459962557)
        ·
          refine ⟨22188134776872202297485959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59168359404992539459962557 22188134776872202297485959)
          ·
            refine ⟨33282202165308303446228939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22188134776872202297485959 33282202165308303446228939)
            ·
              refine ⟨49923303247962455169343409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33282202165308303446228939 49923303247962455169343409)
              ·
                refine ⟨37442477435971841377007557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49923303247962455169343409 37442477435971841377007557)
                ·
                  refine ⟨7020464519244720258188917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37442477435971841377007557 7020464519244720258188917)
                  ·
                    refine ⟨658168548679192524205211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020464519244720258188917 658168548679192524205211)
                    ·
                      rfl

theorem cell22_1922668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1922668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922668 prefixEnd_1922668 := by exact prefixLift 1922668
  have htrace : WordTrace (prefixWord ++ tailWord_1922668) baseStart_1922668 baseEnd_1922668 := by
    simpa [prefixWord, tailWord_1922668, baseEnd_1922668] using wordTrace_append hprefix tailTrace_1922668
  have hstable : (prefixWord ++ tailWord_1922668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922668).length < 2 ^ (prefixWord ++ tailWord_1922668).sum := by decide
  have hdescent : baseEnd_1922668 < baseStart_1922668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922745 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_1922745 : Nat := 118140960795 + 1922745 * 2 ^ 59
def prefixEnd_1922745 : Nat := 4983230072969 + 3 ^ 40 * 1922745 * 2
def baseEnd_1922745 : Nat := 658194907352789990029975

theorem tailTrace_1922745 : CollatzResearch.WordTrace tailWord_1922745 prefixEnd_1922745 658194907352789990029975 := by
  unfold tailWord_1922745
  simp only [CollatzResearch.WordTrace]
  refine ⟨70128271419230718547545689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46752180946153812365030459 70128271419230718547545689)
  ·
    refine ⟨52596203564423038910659267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70128271419230718547545689 52596203564423038910659267)
    ·
      refine ⟨78894305346634558365988901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52596203564423038910659267 78894305346634558365988901)
      ·
        refine ⟨14792682252493979693622919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78894305346634558365988901 14792682252493979693622919)
        ·
          refine ⟨22189023378740969540434379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14792682252493979693622919 22189023378740969540434379)
          ·
            refine ⟨33283535068111454310651569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22189023378740969540434379 33283535068111454310651569)
            ·
              refine ⟨24962651301083590732988677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33283535068111454310651569 24962651301083590732988677)
              ·
                refine ⟨4680497118953173262435377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24962651301083590732988677 4680497118953173262435377)
                ·
                  refine ⟨3510372839214879946826533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680497118953173262435377 3510372839214879946826533)
                  ·
                    refine ⟨658194907352789990029975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3510372839214879946826533 658194907352789990029975)
                    ·
                      rfl

theorem cell22_1922745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_1922745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922745 prefixEnd_1922745 := by exact prefixLift 1922745
  have htrace : WordTrace (prefixWord ++ tailWord_1922745) baseStart_1922745 baseEnd_1922745 := by
    simpa [prefixWord, tailWord_1922745, baseEnd_1922745] using wordTrace_append hprefix tailTrace_1922745
  have hstable : (prefixWord ++ tailWord_1922745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922745).length < 2 ^ (prefixWord ++ tailWord_1922745).sum := by decide
  have hdescent : baseEnd_1922745 < baseStart_1922745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922764 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_1922764 : Nat := 118140960795 + 1922764 * 2 ^ 59
def prefixEnd_1922764 : Nat := 4983230072969 + 3 ^ 40 * 1922764 * 2
def baseEnd_1922764 : Nat := 658201411441080273804917

theorem tailTrace_1922764 : CollatzResearch.WordTrace tailWord_1922764 prefixEnd_1922764 658201411441080273804917 := by
  unfold tailWord_1922764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35064482203080942396243673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46752642937441256528324897 35064482203080942396243673)
  ·
    refine ⟨26298361652310706797182755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35064482203080942396243673 26298361652310706797182755)
    ·
      refine ⟨39447542478466060195774133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26298361652310706797182755 39447542478466060195774133)
      ·
        refine ⟨3698207107356193143353825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39447542478466060195774133 3698207107356193143353825)
        ·
          refine ⟨2773655330517144857515369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698207107356193143353825 2773655330517144857515369)
          ·
            refine ⟨2080241497887858643136527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773655330517144857515369 2080241497887858643136527)
            ·
              refine ⟨3120362246831787964704791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080241497887858643136527 3120362246831787964704791)
              ·
                refine ⟨4680543370247681947057187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120362246831787964704791 4680543370247681947057187)
                ·
                  refine ⟨7020815055371522920585781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680543370247681947057187 7020815055371522920585781)
                  ·
                    refine ⟨658201411441080273804917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020815055371522920585781 658201411441080273804917)
                    ·
                      rfl

theorem cell22_1922764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_1922764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922764 prefixEnd_1922764 := by exact prefixLift 1922764
  have htrace : WordTrace (prefixWord ++ tailWord_1922764) baseStart_1922764 baseEnd_1922764 := by
    simpa [prefixWord, tailWord_1922764, baseEnd_1922764] using wordTrace_append hprefix tailTrace_1922764
  have hstable : (prefixWord ++ tailWord_1922764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922764).length < 2 ^ (prefixWord ++ tailWord_1922764).sum := by decide
  have hdescent : baseEnd_1922764 < baseStart_1922764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922777 : List Nat := [1, 2, 1, 2, 3, 5, 2, 6]
def baseStart_1922777 : Nat := 118140960795 + 1922777 * 2 ^ 59
def prefixEnd_1922777 : Nat := 4983230072969 + 3 ^ 40 * 1922777 * 2
def baseEnd_1922777 : Nat := 73133984622972508136653

theorem tailTrace_1922777 : CollatzResearch.WordTrace tailWord_1922777 prefixEnd_1922777 73133984622972508136653 := by
  unfold tailWord_1922777
  simp only [CollatzResearch.WordTrace]
  refine ⟨70129438555114788012710585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46752959036743192008473723 70129438555114788012710585)
  ·
    refine ⟨52597078916336091009532939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70129438555114788012710585 52597078916336091009532939)
    ·
      refine ⟨78895618374504136514299409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52597078916336091009532939 78895618374504136514299409)
      ·
        refine ⟨59171713780878102385724557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78895618374504136514299409 59171713780878102385724557)
        ·
          refine ⟨22189392667829288394646709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59171713780878102385724557 22189392667829288394646709)
          ·
            refine ⟨2080255562608995786998129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22189392667829288394646709 2080255562608995786998129)
            ·
              refine ⟨1560191671956746840248597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080255562608995786998129 1560191671956746840248597)
              ·
                refine ⟨73133984622972508136653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1560191671956746840248597 73133984622972508136653)
                ·
                  rfl

theorem cell22_1922777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 6].length) (baseStart_1922777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922777 prefixEnd_1922777 := by exact prefixLift 1922777
  have htrace : WordTrace (prefixWord ++ tailWord_1922777) baseStart_1922777 baseEnd_1922777 := by
    simpa [prefixWord, tailWord_1922777, baseEnd_1922777] using wordTrace_append hprefix tailTrace_1922777
  have hstable : (prefixWord ++ tailWord_1922777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922777).length < 2 ^ (prefixWord ++ tailWord_1922777).sum := by decide
  have hdescent : baseEnd_1922777 < baseStart_1922777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922886 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1922886 : Nat := 118140960795 + 1922886 * 2 ^ 59
def prefixEnd_1922886 : Nat := 4983230072969 + 3 ^ 40 * 1922886 * 2
def baseEnd_1922886 : Nat := 658243174534312622254543

theorem tailTrace_1922886 : CollatzResearch.WordTrace tailWord_1922886 prefixEnd_1922886 658243174534312622254543 := by
  unfold tailWord_1922886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191669190991246863388391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46755609407813266418952341 2191669190991246863388391)
  ·
    refine ⟨3287503786486870295082587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191669190991246863388391 3287503786486870295082587)
    ·
      refine ⟨4931255679730305442623881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287503786486870295082587 4931255679730305442623881)
      ·
        refine ⟨3698441759797729081967911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4931255679730305442623881 3698441759797729081967911)
        ·
          refine ⟨5547662639696593622951867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698441759797729081967911 5547662639696593622951867)
          ·
            refine ⟨8321493959544890434427801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547662639696593622951867 8321493959544890434427801)
            ·
              refine ⟨6241120469658667825820851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8321493959544890434427801 6241120469658667825820851)
              ·
                refine ⟨9361680704488001738731277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241120469658667825820851 9361680704488001738731277)
                ·
                  refine ⟨3510630264183000652024229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9361680704488001738731277 3510630264183000652024229)
                  ·
                    refine ⟨658243174534312622254543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3510630264183000652024229 658243174534312622254543)
                    ·
                      rfl

theorem cell22_1922886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1922886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922886 prefixEnd_1922886 := by exact prefixLift 1922886
  have htrace : WordTrace (prefixWord ++ tailWord_1922886) baseStart_1922886 baseEnd_1922886 := by
    simpa [prefixWord, tailWord_1922886, baseEnd_1922886] using wordTrace_append hprefix tailTrace_1922886
  have hstable : (prefixWord ++ tailWord_1922886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922886).length < 2 ^ (prefixWord ++ tailWord_1922886).sum := by decide
  have hdescent : baseEnd_1922886 < baseStart_1922886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922897 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1922897 : Nat := 118140960795 + 1922897 * 2 ^ 59
def prefixEnd_1922897 : Nat := 4983230072969 + 3 ^ 40 * 1922897 * 2
def baseEnd_1922897 : Nat := 658246940059112260229509

theorem tailTrace_1922897 : CollatzResearch.WordTrace tailWord_1922897 prefixEnd_1922897 658246940059112260229509 := by
  unfold tailWord_1922897
  simp only [CollatzResearch.WordTrace]
  refine ⟨70133815314680048507078945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46755876876453365671385963 70133815314680048507078945)
  ·
    refine ⟨52600361486010036380309209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70133815314680048507078945 52600361486010036380309209)
    ·
      refine ⟨39450271114507527285231907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52600361486010036380309209 39450271114507527285231907)
      ·
        refine ⟨59175406671761290927847861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39450271114507527285231907 59175406671761290927847861)
        ·
          refine ⟨5547694375477621024485737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59175406671761290927847861 5547694375477621024485737)
          ·
            refine ⟨4160770781608215768364303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547694375477621024485737 4160770781608215768364303)
            ·
              refine ⟨6241156172412323652546455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160770781608215768364303 6241156172412323652546455)
              ·
                refine ⟨9361734258618485478819683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241156172412323652546455 9361734258618485478819683)
                ·
                  refine ⟨14042601387927728218229525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361734258618485478819683 14042601387927728218229525)
                  ·
                    refine ⟨658246940059112260229509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14042601387927728218229525 658246940059112260229509)
                    ·
                      rfl

theorem cell22_1922897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1922897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922897 prefixEnd_1922897 := by exact prefixLift 1922897
  have htrace : WordTrace (prefixWord ++ tailWord_1922897) baseStart_1922897 baseEnd_1922897 := by
    simpa [prefixWord, tailWord_1922897, baseEnd_1922897] using wordTrace_append hprefix tailTrace_1922897
  have hstable : (prefixWord ++ tailWord_1922897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922897).length < 2 ^ (prefixWord ++ tailWord_1922897).sum := by decide
  have hdescent : baseEnd_1922897 < baseStart_1922897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922903 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 1, 4]
def baseStart_1922903 : Nat := 118140960795 + 1922903 * 2 ^ 59
def prefixEnd_1922903 : Nat := 4983230072969 + 3 ^ 40 * 1922903 * 2
def baseEnd_1922903 : Nat := 658248993981730244579491

theorem tailTrace_1922903 : CollatzResearch.WordTrace tailWord_1922903 prefixEnd_1922903 658248993981730244579491 := by
  unfold tailWord_1922903
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134034152658311531797363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46756022768438874354531575 70134034152658311531797363)
  ·
    refine ⟨105201051228987467297696045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70134034152658311531797363 105201051228987467297696045)
    ·
      refine ⟨39450394210870300236636017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105201051228987467297696045 39450394210870300236636017)
      ·
        refine ⟨29587795658152725177477013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39450394210870300236636017 29587795658152725177477013)
        ·
          refine ⟨1386927921475908992694235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29587795658152725177477013 1386927921475908992694235)
          ·
            refine ⟨2080391882213863489041353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386927921475908992694235 2080391882213863489041353)
            ·
              refine ⟨1560293911660397616781015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080391882213863489041353 1560293911660397616781015)
              ·
                refine ⟨2340440867490596425171523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560293911660397616781015 2340440867490596425171523)
                ·
                  refine ⟨3510661301235894637757285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340440867490596425171523 3510661301235894637757285)
                  ·
                    refine ⟨658248993981730244579491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3510661301235894637757285 658248993981730244579491)
                    ·
                      rfl

theorem cell22_1922903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_1922903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922903 prefixEnd_1922903 := by exact prefixLift 1922903
  have htrace : WordTrace (prefixWord ++ tailWord_1922903) baseStart_1922903 baseEnd_1922903 := by
    simpa [prefixWord, tailWord_1922903, baseEnd_1922903] using wordTrace_append hprefix tailTrace_1922903
  have hstable : (prefixWord ++ tailWord_1922903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922903).length < 2 ^ (prefixWord ++ tailWord_1922903).sum := by decide
  have hdescent : baseEnd_1922903 < baseStart_1922903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922961 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_1922961 : Nat := 118140960795 + 1922961 * 2 ^ 59
def prefixEnd_1922961 : Nat := 4983230072969 + 3 ^ 40 * 1922961 * 2
def baseEnd_1922961 : Nat := 658268848567037426629313

theorem tailTrace_1922961 : CollatzResearch.WordTrace tailWord_1922961 prefixEnd_1922961 658268848567037426629313 := by
  unfold tailWord_1922961
  simp only [CollatzResearch.WordTrace]
  refine ⟨70136149586448187437408737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46757433057632124958272491 70136149586448187437408737)
  ·
    refine ⟨52602112189836140578056553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70136149586448187437408737 52602112189836140578056553)
    ·
      refine ⟨39451584142377105433542415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52602112189836140578056553 39451584142377105433542415)
      ·
        refine ⟨59177376213565658150313623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39451584142377105433542415 59177376213565658150313623)
        ·
          refine ⟨88766064320348487225470435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59177376213565658150313623 88766064320348487225470435)
          ·
            refine ⟨133149096480522730838205653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88766064320348487225470435 133149096480522730838205653)
            ·
              refine ⟨3120681948762251504020445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133149096480522730838205653 3120681948762251504020445)
              ·
                refine ⟨1170255730785844314007667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3120681948762251504020445 1170255730785844314007667)
                ·
                  refine ⟨1755383596178766471011501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170255730785844314007667 1755383596178766471011501)
                  ·
                    refine ⟨658268848567037426629313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755383596178766471011501 658268848567037426629313)
                    ·
                      rfl

theorem cell22_1922961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_1922961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922961 prefixEnd_1922961 := by exact prefixLift 1922961
  have htrace : WordTrace (prefixWord ++ tailWord_1922961) baseStart_1922961 baseEnd_1922961 := by
    simpa [prefixWord, tailWord_1922961, baseEnd_1922961] using wordTrace_append hprefix tailTrace_1922961
  have hstable : (prefixWord ++ tailWord_1922961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922961).length < 2 ^ (prefixWord ++ tailWord_1922961).sum := by decide
  have hdescent : baseEnd_1922961 < baseStart_1922961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922978 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1922978 : Nat := 118140960795 + 1922978 * 2 ^ 59
def prefixEnd_1922978 : Nat := 4983230072969 + 3 ^ 40 * 1922978 * 2
def baseEnd_1922978 : Nat := 658274668014455048954261

theorem tailTrace_1922978 : CollatzResearch.WordTrace tailWord_1922978 prefixEnd_1922978 658274668014455048954261 := by
  unfold tailWord_1922978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534192406846649835194397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46757846418257732893851725 17534192406846649835194397)
  ·
    refine ⟨6575322152567493688197899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17534192406846649835194397 6575322152567493688197899)
    ·
      refine ⟨9862983228851240532296849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575322152567493688197899 9862983228851240532296849)
      ·
        refine ⟨7397237421638430399222637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9862983228851240532296849 7397237421638430399222637)
        ·
          refine ⟨2773964033114411399708489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7397237421638430399222637 2773964033114411399708489)
          ·
            refine ⟨2080473024835808549781367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773964033114411399708489 2080473024835808549781367)
            ·
              refine ⟨3120709537253712824672051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080473024835808549781367 3120709537253712824672051)
              ·
                refine ⟨4681064305880569237008077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120709537253712824672051 4681064305880569237008077)
                ·
                  refine ⟨1755399114705213463878029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4681064305880569237008077 1755399114705213463878029)
                  ·
                    refine ⟨658274668014455048954261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755399114705213463878029 658274668014455048954261)
                    ·
                      rfl

theorem cell22_1922978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1922978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1922978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1922978 prefixEnd_1922978 := by exact prefixLift 1922978
  have htrace : WordTrace (prefixWord ++ tailWord_1922978) baseStart_1922978 baseEnd_1922978 := by
    simpa [prefixWord, tailWord_1922978, baseEnd_1922978] using wordTrace_append hprefix tailTrace_1922978
  have hstable : (prefixWord ++ tailWord_1922978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922978).length < 2 ^ (prefixWord ++ tailWord_1922978).sum := by decide
  have hdescent : baseEnd_1922978 < baseStart_1922978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923017 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_1923017 : Nat := 118140960795 + 1923017 * 2 ^ 59
def prefixEnd_1923017 : Nat := 4983230072969 + 3 ^ 40 * 1923017 * 2
def baseEnd_1923017 : Nat := 658288018511471947229141

theorem tailTrace_1923017 : CollatzResearch.WordTrace tailWord_1923017 prefixEnd_1923017 658288018511471947229141 := by
  unfold tailWord_1923017
  simp only [CollatzResearch.WordTrace]
  refine ⟨70138192074245309001447305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46758794716163539334298203 70138192074245309001447305)
  ·
    refine ⟨52603644055683981751085479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70138192074245309001447305 52603644055683981751085479)
    ·
      refine ⟨78905466083525972626628219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52603644055683981751085479 78905466083525972626628219)
      ·
        refine ⟨118358199125288958939942329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78905466083525972626628219 118358199125288958939942329)
        ·
          refine ⟨88768649343966719204956747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118358199125288958939942329 88768649343966719204956747)
          ·
            refine ⟨133152974015950078807435121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88768649343966719204956747 133152974015950078807435121)
            ·
              refine ⟨99864730511962559105576341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133152974015950078807435121 99864730511962559105576341)
              ·
                refine ⟨4681159242748244958073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99864730511962559105576341 4681159242748244958073891)
                ·
                  refine ⟨7021738864122367437110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681159242748244958073891 7021738864122367437110837)
                  ·
                    refine ⟨658288018511471947229141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7021738864122367437110837 658288018511471947229141)
                    ·
                      rfl

theorem cell22_1923017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_1923017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923017 prefixEnd_1923017 := by exact prefixLift 1923017
  have htrace : WordTrace (prefixWord ++ tailWord_1923017) baseStart_1923017 baseEnd_1923017 := by
    simpa [prefixWord, tailWord_1923017, baseEnd_1923017] using wordTrace_append hprefix tailTrace_1923017
  have hstable : (prefixWord ++ tailWord_1923017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923017).length < 2 ^ (prefixWord ++ tailWord_1923017).sum := by decide
  have hdescent : baseEnd_1923017 < baseStart_1923017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923019 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 4]
def baseStart_1923019 : Nat := 118140960795 + 1923019 * 2 ^ 59
def prefixEnd_1923019 : Nat := 4983230072969 + 3 ^ 40 * 1923019 * 2
def baseEnd_1923019 : Nat := 219429567717448202893045

theorem tailTrace_1923019 : CollatzResearch.WordTrace tailWord_1923019 prefixEnd_1923019 219429567717448202893045 := by
  unfold tailWord_1923019
  simp only [CollatzResearch.WordTrace]
  refine ⟨70138265020238063343020111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46758843346825375562013407 70138265020238063343020111)
  ·
    refine ⟨105207397530357095014530167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70138265020238063343020111 105207397530357095014530167)
    ·
      refine ⟨157811096295535642521795251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105207397530357095014530167 157811096295535642521795251)
      ·
        refine ⟨236716644443303463782692877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157811096295535642521795251 236716644443303463782692877)
        ·
          refine ⟨88768741666238798918509829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236716644443303463782692877 88768741666238798918509829)
          ·
            refine ⟨16644139062419774797220593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88768741666238798918509829 16644139062419774797220593)
            ·
              refine ⟨12483104296814831097915445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16644139062419774797220593 12483104296814831097915445)
              ·
                refine ⟨1170291027826390415429573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12483104296814831097915445 1170291027826390415429573)
                ·
                  refine ⟨219429567717448202893045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170291027826390415429573 219429567717448202893045)
                  ·
                    rfl

theorem cell22_1923019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 4].length) (baseStart_1923019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923019 prefixEnd_1923019 := by exact prefixLift 1923019
  have htrace : WordTrace (prefixWord ++ tailWord_1923019) baseStart_1923019 baseEnd_1923019 := by
    simpa [prefixWord, tailWord_1923019, baseEnd_1923019] using wordTrace_append hprefix tailTrace_1923019
  have hstable : (prefixWord ++ tailWord_1923019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923019).length < 2 ^ (prefixWord ++ tailWord_1923019).sum := by decide
  have hdescent : baseEnd_1923019 < baseStart_1923019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923096 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_1923096 : Nat := 118140960795 + 1923096 * 2 ^ 59
def prefixEnd_1923096 : Nat := 4983230072969 + 3 ^ 40 * 1923096 * 2
def baseEnd_1923096 : Nat := 658315061825942074503899

theorem tailTrace_1923096 : CollatzResearch.WordTrace tailWord_1923096 prefixEnd_1923096 658315061825942074503899 := by
  unfold tailWord_1923096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070536720479552746786571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46760715627306070329048761 35070536720479552746786571)
  ·
    refine ⟨52605805080719329120179857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35070536720479552746786571 52605805080719329120179857)
    ·
      refine ⟨39454353810539496840134893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52605805080719329120179857 39454353810539496840134893)
      ·
        refine ⟨14795382678952311315050585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39454353810539496840134893 14795382678952311315050585)
        ·
          refine ⟨11096537009214233486287939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14795382678952311315050585 11096537009214233486287939)
          ·
            refine ⟨16644805513821350229431909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096537009214233486287939 16644805513821350229431909)
            ·
              refine ⟨3120901033841503168018483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16644805513821350229431909 3120901033841503168018483)
              ·
                refine ⟨4681351550762254752027725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120901033841503168018483 4681351550762254752027725)
                ·
                  refine ⟨1755506831535845532010397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4681351550762254752027725 1755506831535845532010397)
                  ·
                    refine ⟨658315061825942074503899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755506831535845532010397 658315061825942074503899)
                    ·
                      rfl

theorem cell22_1923096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_1923096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923096 prefixEnd_1923096 := by exact prefixLift 1923096
  have htrace : WordTrace (prefixWord ++ tailWord_1923096) baseStart_1923096 baseEnd_1923096 := by
    simpa [prefixWord, tailWord_1923096, baseEnd_1923096] using wordTrace_append hprefix tailTrace_1923096
  have hstable : (prefixWord ++ tailWord_1923096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923096).length < 2 ^ (prefixWord ++ tailWord_1923096).sum := by decide
  have hdescent : baseEnd_1923096 < baseStart_1923096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923169 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1923169 : Nat := 118140960795 + 1923169 * 2 ^ 59
def prefixEnd_1923169 : Nat := 4983230072969 + 3 ^ 40 * 1923169 * 2
def baseEnd_1923169 : Nat := 658340051217794217428675

theorem tailTrace_1923169 : CollatzResearch.WordTrace tailWord_1923169 prefixEnd_1923169 658340051217794217428675 := by
  unfold tailWord_1923169
  simp only [CollatzResearch.WordTrace]
  refine ⟨70143735969694638960980561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46762490646463092640653707 70143735969694638960980561)
  ·
    refine ⟨52607801977270979220735421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70143735969694638960980561 52607801977270979220735421)
    ·
      refine ⟨19727925741476617207775783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52607801977270979220735421 19727925741476617207775783)
      ·
        refine ⟨29591888612214925811663675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727925741476617207775783 29591888612214925811663675)
        ·
          refine ⟨44387832918322388717495513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29591888612214925811663675 44387832918322388717495513)
          ·
            refine ⟨33290874688741791538121635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44387832918322388717495513 33290874688741791538121635)
            ·
              refine ⟨49936312033112687307182453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33290874688741791538121635 49936312033112687307182453)
              ·
                refine ⟨4681529253104314435048355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49936312033112687307182453 4681529253104314435048355)
                ·
                  refine ⟨7022293879656471652572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681529253104314435048355 7022293879656471652572533)
                  ·
                    refine ⟨658340051217794217428675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022293879656471652572533 658340051217794217428675)
                    ·
                      rfl

theorem cell22_1923169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1923169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923169 prefixEnd_1923169 := by exact prefixLift 1923169
  have htrace : WordTrace (prefixWord ++ tailWord_1923169) baseStart_1923169 baseEnd_1923169 := by
    simpa [prefixWord, tailWord_1923169, baseEnd_1923169] using wordTrace_append hprefix tailTrace_1923169
  have hstable : (prefixWord ++ tailWord_1923169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923169).length < 2 ^ (prefixWord ++ tailWord_1923169).sum := by decide
  have hdescent : baseEnd_1923169 < baseStart_1923169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923173 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1923173 : Nat := 118140960795 + 1923173 * 2 ^ 59
def prefixEnd_1923173 : Nat := 4983230072969 + 3 ^ 40 * 1923173 * 2
def baseEnd_1923173 : Nat := 658341420499539540328663

theorem tailTrace_1923173 : CollatzResearch.WordTrace tailWord_1923173 prefixEnd_1923173 658341420499539540328663 := by
  unfold tailWord_1923173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70143881861680147644126173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46762587907786765096084115 70143881861680147644126173)
  ·
    refine ⟨26303955698130055366547315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70143881861680147644126173 26303955698130055366547315)
    ·
      refine ⟨39455933547195083049820973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26303955698130055366547315 39455933547195083049820973)
      ·
        refine ⟨14795975080198156143682865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39455933547195083049820973 14795975080198156143682865)
        ·
          refine ⟨11096981310148617107762149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14795975080198156143682865 11096981310148617107762149)
          ·
            refine ⟨2080683995652865707705403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11096981310148617107762149 2080683995652865707705403)
            ·
              refine ⟨3121025993479298561558105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080683995652865707705403 3121025993479298561558105)
              ·
                refine ⟨2340769495109473921168579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121025993479298561558105 2340769495109473921168579)
                ·
                  refine ⟨3511154242664210881752869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340769495109473921168579 3511154242664210881752869)
                  ·
                    refine ⟨658341420499539540328663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511154242664210881752869 658341420499539540328663)
                    ·
                      rfl

theorem cell22_1923173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1923173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923173 prefixEnd_1923173 := by exact prefixLift 1923173
  have htrace : WordTrace (prefixWord ++ tailWord_1923173) baseStart_1923173 baseEnd_1923173 := by
    simpa [prefixWord, tailWord_1923173, baseEnd_1923173] using wordTrace_append hprefix tailTrace_1923173
  have hstable : (prefixWord ++ tailWord_1923173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923173).length < 2 ^ (prefixWord ++ tailWord_1923173).sum := by decide
  have hdescent : baseEnd_1923173 < baseStart_1923173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923186 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1923186 : Nat := 118140960795 + 1923186 * 2 ^ 59
def prefixEnd_1923186 : Nat := 4983230072969 + 3 ^ 40 * 1923186 * 2
def baseEnd_1923186 : Nat := 658345870665211839753623

theorem tailTrace_1923186 : CollatzResearch.WordTrace tailWord_1923186 prefixEnd_1923186 658345870665211839753623 := by
  unfold tailWord_1923186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536089002658262716087353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46762904007088700576232941 17536089002658262716087353)
  ·
    refine ⟨13152066751993697037065515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17536089002658262716087353 13152066751993697037065515)
    ·
      refine ⟨19728100127990545555598273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13152066751993697037065515 19728100127990545555598273)
      ·
        refine ⟨14796075095992909166698705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19728100127990545555598273 14796075095992909166698705)
        ·
          refine ⟨11097056321994681875024029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14796075095992909166698705 11097056321994681875024029)
          ·
            refine ⟨4161396120748005703134011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11097056321994681875024029 4161396120748005703134011)
            ·
              refine ⟨6242094181122008554701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161396120748005703134011 6242094181122008554701017)
              ·
                refine ⟨4681570635841506416025763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6242094181122008554701017 4681570635841506416025763)
                ·
                  refine ⟨7022355953762259624038645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681570635841506416025763 7022355953762259624038645)
                  ·
                    refine ⟨658345870665211839753623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022355953762259624038645 658345870665211839753623)
                    ·
                      rfl

theorem cell22_1923186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1923186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923186 prefixEnd_1923186 := by exact prefixLift 1923186
  have htrace : WordTrace (prefixWord ++ tailWord_1923186) baseStart_1923186 baseEnd_1923186 := by
    simpa [prefixWord, tailWord_1923186, baseEnd_1923186] using wordTrace_append hprefix tailTrace_1923186
  have hstable : (prefixWord ++ tailWord_1923186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923186).length < 2 ^ (prefixWord ++ tailWord_1923186).sum := by decide
  have hdescent : baseEnd_1923186 < baseStart_1923186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923190 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1923190 : Nat := 118140960795 + 1923190 * 2 ^ 59
def prefixEnd_1923190 : Nat := 4983230072969 + 3 ^ 40 * 1923190 * 2
def baseEnd_1923190 : Nat := 658347239946957162653611

theorem tailTrace_1923190 : CollatzResearch.WordTrace tailWord_1923190 prefixEnd_1923190 658347239946957162653611 := by
  unfold tailWord_1923190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384031368913659971718439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46763001268412373031663349 4384031368913659971718439)
  ·
    refine ⟨6576047053370489957577659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4384031368913659971718439 6576047053370489957577659)
    ·
      refine ⟨9864070580055734936366489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576047053370489957577659 9864070580055734936366489)
      ·
        refine ⟨7398052935041801202274867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9864070580055734936366489 7398052935041801202274867)
        ·
          refine ⟨11097079402562701803412301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398052935041801202274867 11097079402562701803412301)
          ·
            refine ⟨4161404775961013176279613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11097079402562701803412301 4161404775961013176279613)
            ·
              refine ⟨1560526790985379941104855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4161404775961013176279613 1560526790985379941104855)
              ·
                refine ⟨2340790186478069911657283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560526790985379941104855 2340790186478069911657283)
                ·
                  refine ⟨3511185279717104867485925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340790186478069911657283 3511185279717104867485925)
                  ·
                    refine ⟨658347239946957162653611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511185279717104867485925 658347239946957162653611)
                    ·
                      rfl

theorem cell22_1923190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1923190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923190 prefixEnd_1923190 := by exact prefixLift 1923190
  have htrace : WordTrace (prefixWord ++ tailWord_1923190) baseStart_1923190 baseEnd_1923190 := by
    simpa [prefixWord, tailWord_1923190, baseEnd_1923190] using wordTrace_append hprefix tailTrace_1923190
  have hstable : (prefixWord ++ tailWord_1923190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923190).length < 2 ^ (prefixWord ++ tailWord_1923190).sum := by decide
  have hdescent : baseEnd_1923190 < baseStart_1923190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923203 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 2, 3]
def baseStart_1923203 : Nat := 118140960795 + 1923203 * 2 ^ 59
def prefixEnd_1923203 : Nat := 4983230072969 + 3 ^ 40 * 1923203 * 2
def baseEnd_1923203 : Nat := 658351690112629462078571

theorem tailTrace_1923203 : CollatzResearch.WordTrace tailWord_1923203 prefixEnd_1923203 658351690112629462078571 := by
  unfold tailWord_1923203
  simp only [CollatzResearch.WordTrace]
  refine ⟨70144976051571462767718263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46763317367714308511812175 70144976051571462767718263)
  ·
    refine ⟨105217464077357194151577395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70144976051571462767718263 105217464077357194151577395)
    ·
      refine ⟨157826196116035791227366093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105217464077357194151577395 157826196116035791227366093)
      ·
        refine ⟨59184823543513421710262285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157826196116035791227366093 59184823543513421710262285)
        ·
          refine ⟨22194308828817533141348357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59184823543513421710262285 22194308828817533141348357)
          ·
            refine ⟨4161432905403287464002817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22194308828817533141348357 4161432905403287464002817)
            ·
              refine ⟨3121074679052465598002113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161432905403287464002817 3121074679052465598002113)
              ·
                refine ⟨2340806009289349198501585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121074679052465598002113 2340806009289349198501585)
                ·
                  refine ⟨1755604506967011898876189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340806009289349198501585 1755604506967011898876189)
                  ·
                    refine ⟨658351690112629462078571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755604506967011898876189 658351690112629462078571)
                    ·
                      rfl

theorem cell22_1923203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].length) (baseStart_1923203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923203 prefixEnd_1923203 := by exact prefixLift 1923203
  have htrace : WordTrace (prefixWord ++ tailWord_1923203) baseStart_1923203 baseEnd_1923203 := by
    simpa [prefixWord, tailWord_1923203, baseEnd_1923203] using wordTrace_append hprefix tailTrace_1923203
  have hstable : (prefixWord ++ tailWord_1923203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923203).length < 2 ^ (prefixWord ++ tailWord_1923203).sum := by decide
  have hdescent : baseEnd_1923203 < baseStart_1923203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923205 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 4]
def baseStart_1923205 : Nat := 118140960795 + 1923205 * 2 ^ 59
def prefixEnd_1923205 : Nat := 4983230072969 + 3 ^ 40 * 1923205 * 2
def baseEnd_1923205 : Nat := 219450791584500707842855

theorem tailTrace_1923205 : CollatzResearch.WordTrace tailWord_1923205 prefixEnd_1923205 219450791584500707842855 := by
  unfold tailWord_1923205
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145048997564217109291069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46763365998376144739527379 70145048997564217109291069)
  ·
    refine ⟨26304393374086581415984151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70145048997564217109291069 26304393374086581415984151)
    ·
      refine ⟨39456590061129872123976227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26304393374086581415984151 39456590061129872123976227)
      ·
        refine ⟨59184885091694808185964341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39456590061129872123976227 59184885091694808185964341)
        ·
          refine ⟨5548582977346388267434157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59184885091694808185964341 5548582977346388267434157)
          ·
            refine ⟨2080718616504895600287809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5548582977346388267434157 2080718616504895600287809)
            ·
              refine ⟨1560538962378671700215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080718616504895600287809 1560538962378671700215857)
              ·
                refine ⟨1170404221784003775161893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560538962378671700215857 1170404221784003775161893)
                ·
                  refine ⟨219450791584500707842855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170404221784003775161893 219450791584500707842855)
                  ·
                    rfl

theorem cell22_1923205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_1923205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923205 prefixEnd_1923205 := by exact prefixLift 1923205
  have htrace : WordTrace (prefixWord ++ tailWord_1923205) baseStart_1923205 baseEnd_1923205 := by
    simpa [prefixWord, tailWord_1923205, baseEnd_1923205] using wordTrace_append hprefix tailTrace_1923205
  have hstable : (prefixWord ++ tailWord_1923205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923205).length < 2 ^ (prefixWord ++ tailWord_1923205).sum := by decide
  have hdescent : baseEnd_1923205 < baseStart_1923205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923220 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1923220 : Nat := 118140960795 + 1923220 * 2 ^ 59
def prefixEnd_1923220 : Nat := 4983230072969 + 3 ^ 40 * 1923220 * 2
def baseEnd_1923220 : Nat := 658357509560047084403519

theorem tailTrace_1923220 : CollatzResearch.WordTrace tailWord_1923220 prefixEnd_1923220 658357509560047084403519 := by
  unfold tailWord_1923220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35072798046254937335543557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46763730728339916447391409 35072798046254937335543557)
  ·
    refine ⟨6576149633672800750414417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35072798046254937335543557 6576149633672800750414417)
    ·
      refine ⟨4932112225254600562810813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6576149633672800750414417 4932112225254600562810813)
      ·
        refine ⟨1849542084470475211054055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4932112225254600562810813 1849542084470475211054055)
        ·
          refine ⟨2774313126705712816581083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849542084470475211054055 2774313126705712816581083)
          ·
            refine ⟨4161469690058569224871625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774313126705712816581083 4161469690058569224871625)
            ·
              refine ⟨3121102267543926918653719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161469690058569224871625 3121102267543926918653719)
              ·
                refine ⟨4681653401315890377980579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121102267543926918653719 4681653401315890377980579)
                ·
                  refine ⟨7022480101973835566970869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681653401315890377980579 7022480101973835566970869)
                  ·
                    refine ⟨658357509560047084403519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022480101973835566970869 658357509560047084403519)
                    ·
                      rfl

theorem cell22_1923220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1923220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923220 prefixEnd_1923220 := by exact prefixLift 1923220
  have htrace : WordTrace (prefixWord ++ tailWord_1923220) baseStart_1923220 baseEnd_1923220 := by
    simpa [prefixWord, tailWord_1923220, baseEnd_1923220] using wordTrace_append hprefix tailTrace_1923220
  have hstable : (prefixWord ++ tailWord_1923220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923220).length < 2 ^ (prefixWord ++ tailWord_1923220).sum := by decide
  have hdescent : baseEnd_1923220 < baseStart_1923220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923259 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_1923259 : Nat := 118140960795 + 1923259 * 2 ^ 59
def prefixEnd_1923259 : Nat := 4983230072969 + 3 ^ 40 * 1923259 * 2
def baseEnd_1923259 : Nat := 658370860057063982678399

theorem tailTrace_1923259 : CollatzResearch.WordTrace tailWord_1923259 prefixEnd_1923259 658370860057063982678399 := by
  unfold tailWord_1923259
  simp only [CollatzResearch.WordTrace]
  refine ⟨70147018539368584331756831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46764679026245722887837887 70147018539368584331756831)
  ·
    refine ⟨105220527809052876497635247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70147018539368584331756831 105220527809052876497635247)
    ·
      refine ⟨157830791713579314746452871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105220527809052876497635247 157830791713579314746452871)
      ·
        refine ⟨236746187570368972119679307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157830791713579314746452871 236746187570368972119679307)
        ·
          refine ⟨355119281355553458179518961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236746187570368972119679307 355119281355553458179518961)
          ·
            refine ⟨266339461016665093634639221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355119281355553458179518961 266339461016665093634639221)
            ·
              refine ⟨24969324470312352528247427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266339461016665093634639221 24969324470312352528247427)
              ·
                refine ⟨37453986705468528792371141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24969324470312352528247427 37453986705468528792371141)
                ·
                  refine ⟨7022622507275349148569589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37453986705468528792371141 7022622507275349148569589)
                  ·
                    refine ⟨658370860057063982678399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022622507275349148569589 658370860057063982678399)
                    ·
                      rfl

theorem cell22_1923259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_1923259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923259 prefixEnd_1923259 := by exact prefixLift 1923259
  have htrace : WordTrace (prefixWord ++ tailWord_1923259) baseStart_1923259 baseEnd_1923259 := by
    simpa [prefixWord, tailWord_1923259, baseEnd_1923259] using wordTrace_append hprefix tailTrace_1923259
  have hstable : (prefixWord ++ tailWord_1923259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923259).length < 2 ^ (prefixWord ++ tailWord_1923259).sum := by decide
  have hdescent : baseEnd_1923259 < baseStart_1923259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923291 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 1, 4]
def baseStart_1923291 : Nat := 118140960795 + 1923291 * 2 ^ 59
def prefixEnd_1923291 : Nat := 4983230072969 + 3 ^ 40 * 1923291 * 2
def baseEnd_1923291 : Nat := 658381814311026565878301

theorem tailTrace_1923291 : CollatzResearch.WordTrace tailWord_1923291 prefixEnd_1923291 658381814311026565878301 := by
  unfold tailWord_1923291
  simp only [CollatzResearch.WordTrace]
  refine ⟨70148185675252653796921727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46765457116835102531281151 70148185675252653796921727)
  ·
    refine ⟨105222278512878980695382591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70148185675252653796921727 105222278512878980695382591)
    ·
      refine ⟨157833417769318471043073887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105222278512878980695382591 157833417769318471043073887)
      ·
        refine ⟨236750126653977706564610831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157833417769318471043073887 236750126653977706564610831)
        ·
          refine ⟨355125189980966559846916247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236750126653977706564610831 355125189980966559846916247)
          ·
            refine ⟨532687784971449839770374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355125189980966559846916247 532687784971449839770374371)
            ·
              refine ⟨799031677457174759655561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532687784971449839770374371 799031677457174759655561557)
              ·
                refine ⟨2340913117550316678678403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 799031677457174759655561557 2340913117550316678678403)
                ·
                  refine ⟨3511369676325475018017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340913117550316678678403 3511369676325475018017605)
                  ·
                    refine ⟨658381814311026565878301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511369676325475018017605 658381814311026565878301)
                    ·
                      rfl

theorem cell22_1923291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_1923291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923291 prefixEnd_1923291 := by exact prefixLift 1923291
  have htrace : WordTrace (prefixWord ++ tailWord_1923291) baseStart_1923291 baseEnd_1923291 := by
    simpa [prefixWord, tailWord_1923291, baseEnd_1923291] using wordTrace_append hprefix tailTrace_1923291
  have hstable : (prefixWord ++ tailWord_1923291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923291).length < 2 ^ (prefixWord ++ tailWord_1923291).sum := by decide
  have hdescent : baseEnd_1923291 < baseStart_1923291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923299 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 1, 3]
def baseStart_1923299 : Nat := 118140960795 + 1923299 * 2 ^ 59
def prefixEnd_1923299 : Nat := 4983230072969 + 3 ^ 40 * 1923299 * 2
def baseEnd_1923299 : Nat := 658384552874517211678277

theorem tailTrace_1923299 : CollatzResearch.WordTrace tailWord_1923299 prefixEnd_1923299 658384552874517211678277 := by
  unfold tailWord_1923299
  simp only [CollatzResearch.WordTrace]
  refine ⟨70148477459223671163212951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46765651639482447442141967 70148477459223671163212951)
  ·
    refine ⟨105222716188835506744819427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70148477459223671163212951 105222716188835506744819427)
    ·
      refine ⟨157834074283253260117229141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105222716188835506744819427 157834074283253260117229141)
      ·
        refine ⟨1849618058006874141998779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 157834074283253260117229141 1849618058006874141998779)
        ·
          refine ⟨2774427087010311212998169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849618058006874141998779 2774427087010311212998169)
          ·
            refine ⟨2080820315257733409748627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774427087010311212998169 2080820315257733409748627)
            ·
              refine ⟨3121230472886600114622941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080820315257733409748627 3121230472886600114622941)
              ·
                refine ⟨1170461427332475042983603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3121230472886600114622941 1170461427332475042983603)
                ·
                  refine ⟨1755692140998712564475405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170461427332475042983603 1755692140998712564475405)
                  ·
                    refine ⟨658384552874517211678277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755692140998712564475405 658384552874517211678277)
                    ·
                      rfl

theorem cell22_1923299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 3].length) (baseStart_1923299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923299 prefixEnd_1923299 := by exact prefixLift 1923299
  have htrace : WordTrace (prefixWord ++ tailWord_1923299) baseStart_1923299 baseEnd_1923299 := by
    simpa [prefixWord, tailWord_1923299, baseEnd_1923299] using wordTrace_append hprefix tailTrace_1923299
  have hstable : (prefixWord ++ tailWord_1923299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923299).length < 2 ^ (prefixWord ++ tailWord_1923299).sum := by decide
  have hdescent : baseEnd_1923299 < baseStart_1923299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923351 : List Nat := [1, 1, 3, 4, 1, 2, 2, 8]
def baseStart_1923351 : Nat := 118140960795 + 1923351 * 2 ^ 59
def prefixEnd_1923351 : Nat := 4983230072969 + 3 ^ 40 * 1923351 * 2
def baseEnd_1923351 : Nat := 73155817059689601042013

theorem tailTrace_1923351 : CollatzResearch.WordTrace tailWord_1923351 prefixEnd_1923351 73155817059689601042013 := by
  unfold tailWord_1923351
  simp only [CollatzResearch.WordTrace]
  refine ⟨70150374055035284044105907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46766916036690189362737271 70150374055035284044105907)
  ·
    refine ⟨105225561082552926066158861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70150374055035284044105907 105225561082552926066158861)
    ·
      refine ⟨39459585405957347274809573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105225561082552926066158861 39459585405957347274809573)
      ·
        refine ⟨7398672263617002614026795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39459585405957347274809573 7398672263617002614026795)
        ·
          refine ⟨11098008395425503921040193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398672263617002614026795 11098008395425503921040193)
          ·
            refine ⟨8323506296569127940780145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11098008395425503921040193 8323506296569127940780145)
            ·
              refine ⟨6242629722426845955585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323506296569127940780145 6242629722426845955585109)
              ·
                refine ⟨73155817059689601042013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6242629722426845955585109 73155817059689601042013)
                ·
                  rfl

theorem cell22_1923351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 8].length) (baseStart_1923351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923351 prefixEnd_1923351 := by exact prefixLift 1923351
  have htrace : WordTrace (prefixWord ++ tailWord_1923351) baseStart_1923351 baseEnd_1923351 := by
    simpa [prefixWord, tailWord_1923351, baseEnd_1923351] using wordTrace_append hprefix tailTrace_1923351
  have hstable : (prefixWord ++ tailWord_1923351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923351).length < 2 ^ (prefixWord ++ tailWord_1923351).sum := by decide
  have hdescent : baseEnd_1923351 < baseStart_1923351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923368 : List Nat := [2, 1, 5, 1, 4, 9]
def baseStart_1923368 : Nat := 118140960795 + 1923368 * 2 ^ 59
def prefixEnd_1923368 : Nat := 4983230072969 + 3 ^ 40 * 1923368 * 2
def baseEnd_1923368 : Nat := 8128495962773136193865

theorem tailTrace_1923368 : CollatzResearch.WordTrace tailWord_1923368 prefixEnd_1923368 8128495962773136193865 := by
  unfold tailWord_1923368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35075497047986847973737379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46767329397315797298316505 35075497047986847973737379)
  ·
    refine ⟨52613245571980271960606069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35075497047986847973737379 52613245571980271960606069)
    ·
      refine ⟨4932491772373150496306819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52613245571980271960606069 4932491772373150496306819)
      ·
        refine ⟨7398737658559725744460229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932491772373150496306819 7398737658559725744460229)
        ·
          refine ⟨1387263310979948577086293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7398737658559725744460229 1387263310979948577086293)
          ·
            refine ⟨8128495962773136193865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1387263310979948577086293 8128495962773136193865)
            ·
              rfl

theorem cell22_1923368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 9].length) (baseStart_1923368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923368 prefixEnd_1923368 := by exact prefixLift 1923368
  have htrace : WordTrace (prefixWord ++ tailWord_1923368) baseStart_1923368 baseEnd_1923368 := by
    simpa [prefixWord, tailWord_1923368, baseEnd_1923368] using wordTrace_append hprefix tailTrace_1923368
  have hstable : (prefixWord ++ tailWord_1923368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923368).length < 2 ^ (prefixWord ++ tailWord_1923368).sum := by decide
  have hdescent : baseEnd_1923368 < baseStart_1923368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923381 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1923381 : Nat := 118140960795 + 1923381 * 2 ^ 59
def prefixEnd_1923381 : Nat := 4983230072969 + 3 ^ 40 * 1923381 * 2
def baseEnd_1923381 : Nat := 658412623150296331128025

theorem tailTrace_1923381 : CollatzResearch.WordTrace tailWord_1923381 prefixEnd_1923381 658412623150296331128025 := by
  unfold tailWord_1923381
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151468244926599167697997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46767645496617732778465331 70151468244926599167697997)
  ·
    refine ⟨26306800591847474687886749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70151468244926599167697997 26306800591847474687886749)
    ·
      refine ⟨9865050221942803007957531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26306800591847474687886749 9865050221942803007957531)
      ·
        refine ⟨14797575332914204511936297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865050221942803007957531 14797575332914204511936297)
        ·
          refine ⟨11098181499685653383952223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14797575332914204511936297 11098181499685653383952223)
          ·
            refine ⟨16647272249528480075928335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098181499685653383952223 16647272249528480075928335)
            ·
              refine ⟨24970908374292720113892503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647272249528480075928335 24970908374292720113892503)
              ·
                refine ⟨37456362561439080170838755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24970908374292720113892503 37456362561439080170838755)
                ·
                  refine ⟨56184543842158620256258133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37456362561439080170838755 56184543842158620256258133)
                  ·
                    refine ⟨658412623150296331128025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56184543842158620256258133 658412623150296331128025)
                    ·
                      rfl

theorem cell22_1923381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1923381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923381 prefixEnd_1923381 := by exact prefixLift 1923381
  have htrace : WordTrace (prefixWord ++ tailWord_1923381) baseStart_1923381 baseEnd_1923381 := by
    simpa [prefixWord, tailWord_1923381, baseEnd_1923381] using wordTrace_append hprefix tailTrace_1923381
  have hstable : (prefixWord ++ tailWord_1923381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923381).length < 2 ^ (prefixWord ++ tailWord_1923381).sum := by decide
  have hdescent : baseEnd_1923381 < baseStart_1923381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923460 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1923460 : Nat := 118140960795 + 1923460 * 2 ^ 59
def prefixEnd_1923460 : Nat := 4983230072969 + 3 ^ 40 * 1923460 * 2
def baseEnd_1923460 : Nat := 658439666464766458402783

theorem tailTrace_1923460 : CollatzResearch.WordTrace tailWord_1923460 prefixEnd_1923460 658439666464766458402783 := by
  unfold tailWord_1923460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077174805820197829911917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46769566407760263773215889 35077174805820197829911917)
  ·
    refine ⟨13153940552182574186216969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35077174805820197829911917 13153940552182574186216969)
    ·
      refine ⟨9865455414136930639662727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13153940552182574186216969 9865455414136930639662727)
      ·
        refine ⟨14798183121205395959494091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865455414136930639662727 14798183121205395959494091)
        ·
          refine ⟨22197274681808093939241137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798183121205395959494091 22197274681808093939241137)
          ·
            refine ⟨16647956011356070454430853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197274681808093939241137 16647956011356070454430853)
            ·
              refine ⟨3121491752129263210205785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16647956011356070454430853 3121491752129263210205785)
              ·
                refine ⟨2341118814096947407654339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121491752129263210205785 2341118814096947407654339)
                ·
                  refine ⟨3511678221145421111481509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341118814096947407654339 3511678221145421111481509)
                  ·
                    refine ⟨658439666464766458402783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511678221145421111481509 658439666464766458402783)
                    ·
                      rfl

theorem cell22_1923460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1923460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923460 prefixEnd_1923460 := by exact prefixLift 1923460
  have htrace : WordTrace (prefixWord ++ tailWord_1923460) baseStart_1923460 baseEnd_1923460 := by
    simpa [prefixWord, tailWord_1923460, baseEnd_1923460] using wordTrace_append hprefix tailTrace_1923460
  have hstable : (prefixWord ++ tailWord_1923460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923460).length < 2 ^ (prefixWord ++ tailWord_1923460).sum := by decide
  have hdescent : baseEnd_1923460 < baseStart_1923460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923488 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_1923488 : Nat := 118140960795 + 1923488 * 2 ^ 59
def prefixEnd_1923488 : Nat := 4983230072969 + 3 ^ 40 * 1923488 * 2
def baseEnd_1923488 : Nat := 658449251436983718702697

theorem tailTrace_1923488 : CollatzResearch.WordTrace tailWord_1923488 prefixEnd_1923488 658449251436983718702697 := by
  unfold tailWord_1923488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077685427769478220921559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46770247237025970961228745 35077685427769478220921559)
  ·
    refine ⟨52616528141654217331382339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35077685427769478220921559 52616528141654217331382339)
    ·
      refine ⟨78924792212481325997073509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52616528141654217331382339 78924792212481325997073509)
      ·
        refine ⟨14798398539840248624451283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78924792212481325997073509 14798398539840248624451283)
        ·
          refine ⟨22197597809760372936676925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798398539840248624451283 22197597809760372936676925)
          ·
            refine ⟨8324099178660139851253847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22197597809760372936676925 8324099178660139851253847)
            ·
              refine ⟨12486148767990209776880771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324099178660139851253847 12486148767990209776880771)
              ·
                refine ⟨18729223151985314665321157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12486148767990209776880771 18729223151985314665321157)
                ·
                  refine ⟨3511729340997246499747717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18729223151985314665321157 3511729340997246499747717)
                  ·
                    refine ⟨658449251436983718702697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511729340997246499747717 658449251436983718702697)
                    ·
                      rfl

theorem cell22_1923488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_1923488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923488 prefixEnd_1923488 := by exact prefixLift 1923488
  have htrace : WordTrace (prefixWord ++ tailWord_1923488) baseStart_1923488 baseEnd_1923488 := by
    simpa [prefixWord, tailWord_1923488, baseEnd_1923488] using wordTrace_append hprefix tailTrace_1923488
  have hstable : (prefixWord ++ tailWord_1923488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923488).length < 2 ^ (prefixWord ++ tailWord_1923488).sum := by decide
  have hdescent : baseEnd_1923488 < baseStart_1923488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923490 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1923490 : Nat := 118140960795 + 1923490 * 2 ^ 59
def prefixEnd_1923490 : Nat := 4983230072969 + 3 ^ 40 * 1923490 * 2
def baseEnd_1923490 : Nat := 658449936077856380152691

theorem tailTrace_1923490 : CollatzResearch.WordTrace tailWord_1923490 prefixEnd_1923490 658449936077856380152691 := by
  unfold tailWord_1923490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538860950382927695853981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46770295867687807188943949 17538860950382927695853981)
  ·
    refine ⟨6577072856393597885945243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17538860950382927695853981 6577072856393597885945243)
    ·
      refine ⟨9865609284590396828917865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577072856393597885945243 9865609284590396828917865)
      ·
        refine ⟨7399206963442797621688399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9865609284590396828917865 7399206963442797621688399)
        ·
          refine ⟨11098810445164196432532599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399206963442797621688399 11098810445164196432532599)
          ·
            refine ⟨16648215667746294648798899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098810445164196432532599 16648215667746294648798899)
            ·
              refine ⟨24972323501619441973198349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648215667746294648798899 24972323501619441973198349)
              ·
                refine ⟨9364621313107290739949381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24972323501619441973198349 9364621313107290739949381)
                ·
                  refine ⟨1755866496207617013740509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9364621313107290739949381 1755866496207617013740509)
                  ·
                    refine ⟨658449936077856380152691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755866496207617013740509 658449936077856380152691)
                    ·
                      rfl

theorem cell22_1923490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1923490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923490 prefixEnd_1923490 := by exact prefixLift 1923490
  have htrace : WordTrace (prefixWord ++ tailWord_1923490) baseStart_1923490 baseEnd_1923490 := by
    simpa [prefixWord, tailWord_1923490, baseEnd_1923490] using wordTrace_append hprefix tailTrace_1923490
  have hstable : (prefixWord ++ tailWord_1923490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923490).length < 2 ^ (prefixWord ++ tailWord_1923490).sum := by decide
  have hdescent : baseEnd_1923490 < baseStart_1923490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923498 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_1923498 : Nat := 118140960795 + 1923498 * 2 ^ 59
def prefixEnd_1923498 : Nat := 4983230072969 + 3 ^ 40 * 1923498 * 2
def baseEnd_1923498 : Nat := 219484224880449008650889

theorem tailTrace_1923498 : CollatzResearch.WordTrace tailWord_1923498 prefixEnd_1923498 219484224880449008650889 := by
  unfold tailWord_1923498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538933896375682037426787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46770490390335152099804765 17538933896375682037426787)
  ·
    refine ⟨26308400844563523056140181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17538933896375682037426787 26308400844563523056140181)
    ·
      refine ⟨1233206289588915143256571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26308400844563523056140181 1233206289588915143256571)
      ·
        refine ⟨1849809434383372714884857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233206289588915143256571 1849809434383372714884857)
        ·
          refine ⟨1387357075787529536163643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849809434383372714884857 1387357075787529536163643)
          ·
            refine ⟨2081035613681294304245465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387357075787529536163643 2081035613681294304245465)
            ·
              refine ⟨1560776710260970728184099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081035613681294304245465 1560776710260970728184099)
              ·
                refine ⟨2341165065391456092276149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560776710260970728184099 2341165065391456092276149)
                ·
                  refine ⟨219484224880449008650889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341165065391456092276149 219484224880449008650889)
                  ·
                    rfl

theorem cell22_1923498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_1923498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923498 prefixEnd_1923498 := by exact prefixLift 1923498
  have htrace : WordTrace (prefixWord ++ tailWord_1923498) baseStart_1923498 baseEnd_1923498 := by
    simpa [prefixWord, tailWord_1923498, baseEnd_1923498] using wordTrace_append hprefix tailTrace_1923498
  have hstable : (prefixWord ++ tailWord_1923498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923498).length < 2 ^ (prefixWord ++ tailWord_1923498).sum := by decide
  have hdescent : baseEnd_1923498 < baseStart_1923498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923518 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1923518 : Nat := 118140960795 + 1923518 * 2 ^ 59
def prefixEnd_1923518 : Nat := 4983230072969 + 3 ^ 40 * 1923518 * 2
def baseEnd_1923518 : Nat := 658459521050073640452605

theorem tailTrace_1923518 : CollatzResearch.WordTrace tailWord_1923518 prefixEnd_1923518 658459521050073640452605 := by
  unfold tailWord_1923518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769558130678783945679401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46770976696953514376956805 8769558130678783945679401)
  ·
    refine ⟨6577168598009087959259551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8769558130678783945679401 6577168598009087959259551)
    ·
      refine ⟨9865752897013631938889327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577168598009087959259551 9865752897013631938889327)
      ·
        refine ⟨14798629345520447908333991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865752897013631938889327 14798629345520447908333991)
        ·
          refine ⟨22197944018280671862500987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798629345520447908333991 22197944018280671862500987)
          ·
            refine ⟨33296916027421007793751481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22197944018280671862500987 33296916027421007793751481)
            ·
              refine ⟨24972687020565755845313611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33296916027421007793751481 24972687020565755845313611)
              ·
                refine ⟨37459030530848633767970417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24972687020565755845313611 37459030530848633767970417)
                ·
                  refine ⟨28094272898136475325977813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37459030530848633767970417 28094272898136475325977813)
                  ·
                    refine ⟨658459521050073640452605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28094272898136475325977813 658459521050073640452605)
                    ·
                      rfl

theorem cell22_1923518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1923518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923518 prefixEnd_1923518 := by exact prefixLift 1923518
  have htrace : WordTrace (prefixWord ++ tailWord_1923518) baseStart_1923518 baseEnd_1923518 := by
    simpa [prefixWord, tailWord_1923518, baseEnd_1923518] using wordTrace_append hprefix tailTrace_1923518
  have hstable : (prefixWord ++ tailWord_1923518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923518).length < 2 ^ (prefixWord ++ tailWord_1923518).sum := by decide
  have hdescent : baseEnd_1923518 < baseStart_1923518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923552 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_1923552 : Nat := 118140960795 + 1923552 * 2 ^ 59
def prefixEnd_1923552 : Nat := 4983230072969 + 3 ^ 40 * 1923552 * 2
def baseEnd_1923552 : Nat := 658471159944908885102501

theorem tailTrace_1923552 : CollatzResearch.WordTrace tailWord_1923552 prefixEnd_1923552 658471159944908885102501 := by
  unfold tailWord_1923552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35078852563653547686086455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46771803418204730248115273 35078852563653547686086455)
  ·
    refine ⟨52618278845480321529129683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35078852563653547686086455 52618278845480321529129683)
    ·
      refine ⟨78927418268220482293694525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52618278845480321529129683 78927418268220482293694525)
      ·
        refine ⟨29597781850582680860135447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78927418268220482293694525 29597781850582680860135447)
        ·
          refine ⟨44396672775874021290203171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29597781850582680860135447 44396672775874021290203171)
          ·
            refine ⟨66595009163811031935304757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44396672775874021290203171 66595009163811031935304757)
            ·
              refine ⟨6243282109107284243934821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66595009163811031935304757 6243282109107284243934821)
              ·
                refine ⟨1170615395457615795737779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6243282109107284243934821 1170615395457615795737779)
                ·
                  refine ⟨1755923093186423693606669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170615395457615795737779 1755923093186423693606669)
                  ·
                    refine ⟨658471159944908885102501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755923093186423693606669 658471159944908885102501)
                    ·
                      rfl

theorem cell22_1923552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_1923552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923552 prefixEnd_1923552 := by exact prefixLift 1923552
  have htrace : WordTrace (prefixWord ++ tailWord_1923552) baseStart_1923552 baseEnd_1923552 := by
    simpa [prefixWord, tailWord_1923552, baseEnd_1923552] using wordTrace_append hprefix tailTrace_1923552
  have hstable : (prefixWord ++ tailWord_1923552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923552).length < 2 ^ (prefixWord ++ tailWord_1923552).sum := by decide
  have hdescent : baseEnd_1923552 < baseStart_1923552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923554 : List Nat := [3, 3, 3, 2, 1, 2, 1, 7]
def baseStart_1923554 : Nat := 118140960795 + 1923554 * 2 ^ 59
def prefixEnd_1923554 : Nat := 4983230072969 + 3 ^ 40 * 1923554 * 2
def baseEnd_1923554 : Nat := 73163538287309060728055

theorem tailTrace_1923554 : CollatzResearch.WordTrace tailWord_1923554 prefixEnd_1923554 73163538287309060728055 := by
  unfold tailWord_1923554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17539444518324962428436429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46771852048866566475830477 17539444518324962428436429)
  ·
    refine ⟨6577291694371860910663661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17539444518324962428436429 6577291694371860910663661)
    ·
      refine ⟨2466484385389447841498873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6577291694371860910663661 2466484385389447841498873)
      ·
        refine ⟨1849863289042085881124155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466484385389447841498873 1849863289042085881124155)
        ·
          refine ⟨2774794933563128821686233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849863289042085881124155 2774794933563128821686233)
          ·
            refine ⟨2081096200172346616264675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774794933563128821686233 2081096200172346616264675)
            ·
              refine ⟨3121644300258519924397013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081096200172346616264675 3121644300258519924397013)
              ·
                refine ⟨73163538287309060728055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3121644300258519924397013 73163538287309060728055)
                ·
                  rfl

theorem cell22_1923554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_1923554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923554 prefixEnd_1923554 := by exact prefixLift 1923554
  have htrace : WordTrace (prefixWord ++ tailWord_1923554) baseStart_1923554 baseEnd_1923554 := by
    simpa [prefixWord, tailWord_1923554, baseEnd_1923554] using wordTrace_append hprefix tailTrace_1923554
  have hstable : (prefixWord ++ tailWord_1923554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923554).length < 2 ^ (prefixWord ++ tailWord_1923554).sum := by decide
  have hdescent : baseEnd_1923554 < baseStart_1923554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923563 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_1923563 : Nat := 118140960795 + 1923563 * 2 ^ 59
def prefixEnd_1923563 : Nat := 4983230072969 + 3 ^ 40 * 1923563 * 2
def baseEnd_1923563 : Nat := 658474925469708523077467

theorem tailTrace_1923563 : CollatzResearch.WordTrace tailWord_1923563 prefixEnd_1923563 658474925469708523077467 := by
  unfold tailWord_1923563
  simp only [CollatzResearch.WordTrace]
  refine ⟨70158106330267244250823343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46772070886844829500548895 70158106330267244250823343)
  ·
    refine ⟨105237159495400866376235015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70158106330267244250823343 105237159495400866376235015)
    ·
      refine ⟨157855739243101299564352523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105237159495400866376235015 157855739243101299564352523)
      ·
        refine ⟨236783608864651949346528785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157855739243101299564352523 236783608864651949346528785)
        ·
          refine ⟨177587706648488962009896589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236783608864651949346528785 177587706648488962009896589)
          ·
            refine ⟨66595389993183360753711221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177587706648488962009896589 66595389993183360753711221)
            ·
              refine ⟨6243317811860940070660427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66595389993183360753711221 6243317811860940070660427)
              ·
                refine ⟨9364976717791410105990641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243317811860940070660427 9364976717791410105990641)
                ·
                  refine ⟨7023732538343557579492981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364976717791410105990641 7023732538343557579492981)
                  ·
                    refine ⟨658474925469708523077467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7023732538343557579492981 658474925469708523077467)
                    ·
                      rfl

theorem cell22_1923563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_1923563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923563 prefixEnd_1923563 := by exact prefixLift 1923563
  have htrace : WordTrace (prefixWord ++ tailWord_1923563) baseStart_1923563 baseEnd_1923563 := by
    simpa [prefixWord, tailWord_1923563, baseEnd_1923563] using wordTrace_append hprefix tailTrace_1923563
  have hstable : (prefixWord ++ tailWord_1923563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923563).length < 2 ^ (prefixWord ++ tailWord_1923563).sum := by decide
  have hdescent : baseEnd_1923563 < baseStart_1923563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923640 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_1923640 : Nat := 118140960795 + 1923640 * 2 ^ 59
def prefixEnd_1923640 : Nat := 4983230072969 + 3 ^ 40 * 1923640 * 2
def baseEnd_1923640 : Nat := 658501284143305988902231

theorem tailTrace_1923640 : CollatzResearch.WordTrace tailWord_1923640 prefixEnd_1923640 658501284143305988902231 := by
  unfold tailWord_1923640
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080457375494143200688187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46773943167325524267584249 35080457375494143200688187)
  ·
    refine ⟨52620686063241214801032281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35080457375494143200688187 52620686063241214801032281)
    ·
      refine ⟨39465514547430911100774211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52620686063241214801032281 39465514547430911100774211)
      ·
        refine ⟨59198271821146366651161317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39465514547430911100774211 59198271821146366651161317)
        ·
          refine ⟨11099675966464943747092747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59198271821146366651161317 11099675966464943747092747)
          ·
            refine ⟨16649513949697415620639121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099675966464943747092747 16649513949697415620639121)
            ·
              refine ⟨12487135462273061715479341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16649513949697415620639121 12487135462273061715479341)
              ·
                refine ⟨4682675798352398143304753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12487135462273061715479341 4682675798352398143304753)
                ·
                  refine ⟨3512006848764298607478565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682675798352398143304753 3512006848764298607478565)
                  ·
                    refine ⟨658501284143305988902231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3512006848764298607478565 658501284143305988902231)
                    ·
                      rfl

theorem cell22_1923640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_1923640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923640 prefixEnd_1923640 := by exact prefixLift 1923640
  have htrace : WordTrace (prefixWord ++ tailWord_1923640) baseStart_1923640 baseEnd_1923640 := by
    simpa [prefixWord, tailWord_1923640, baseEnd_1923640] using wordTrace_append hprefix tailTrace_1923640
  have hstable : (prefixWord ++ tailWord_1923640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923640).length < 2 ^ (prefixWord ++ tailWord_1923640).sum := by decide
  have hdescent : baseEnd_1923640 < baseStart_1923640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923644 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1923644 : Nat := 118140960795 + 1923644 * 2 ^ 59
def prefixEnd_1923644 : Nat := 4983230072969 + 3 ^ 40 * 1923644 * 2
def baseEnd_1923644 : Nat := 219500884475017103934073

theorem tailTrace_1923644 : CollatzResearch.WordTrace tailWord_1923644 prefixEnd_1923644 219500884475017103934073 := by
  unfold tailWord_1923644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080530321486897542260993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46774040428649196723014657 35080530321486897542260993)
  ·
    refine ⟨26310397741115173156695745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35080530321486897542260993 26310397741115173156695745)
    ·
      refine ⟨19732798305836379867521809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26310397741115173156695745 19732798305836379867521809)
      ·
        refine ⟨14799598729377284900641357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19732798305836379867521809 14799598729377284900641357)
        ·
          refine ⟨5549849523516481837740509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14799598729377284900641357 5549849523516481837740509)
          ·
            refine ⟨2081193571318680689152691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5549849523516481837740509 2081193571318680689152691)
            ·
              refine ⟨3121790356978021033729037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081193571318680689152691 3121790356978021033729037)
              ·
                refine ⟨1170671383866757887648389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3121790356978021033729037 1170671383866757887648389)
                ·
                  refine ⟨219500884475017103934073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170671383866757887648389 219500884475017103934073)
                  ·
                    rfl

theorem cell22_1923644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1923644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923644 prefixEnd_1923644 := by exact prefixLift 1923644
  have htrace : WordTrace (prefixWord ++ tailWord_1923644) baseStart_1923644 baseEnd_1923644 := by
    simpa [prefixWord, tailWord_1923644, baseEnd_1923644] using wordTrace_append hprefix tailTrace_1923644
  have hstable : (prefixWord ++ tailWord_1923644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923644).length < 2 ^ (prefixWord ++ tailWord_1923644).sum := by decide
  have hdescent : baseEnd_1923644 < baseStart_1923644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923655 : List Nat := [1, 1, 4, 1, 4, 3, 8]
def baseStart_1923655 : Nat := 118140960795 + 1923655 * 2 ^ 59
def prefixEnd_1923655 : Nat := 4983230072969 + 3 ^ 40 * 1923655 * 2
def baseEnd_1923655 : Nat := 24389126627772257399155

theorem tailTrace_1923655 : CollatzResearch.WordTrace tailWord_1923655 prefixEnd_1923655 24389126627772257399155 := by
  unfold tailWord_1923655
  simp only [CollatzResearch.WordTrace]
  refine ⟨70161461845933943963172419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46774307897289295975448279 70161461845933943963172419)
  ·
    refine ⟨105242192768900915944758629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70161461845933943963172419 105242192768900915944758629)
    ·
      refine ⟨19732911144168921739642243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105242192768900915944758629 19732911144168921739642243)
      ·
        refine ⟨29599366716253382609463365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732911144168921739642243 29599366716253382609463365)
        ·
          refine ⟨5549881259297509239274381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29599366716253382609463365 5549881259297509239274381)
          ·
            refine ⟨2081205472236565964727893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5549881259297509239274381 2081205472236565964727893)
            ·
              refine ⟨24389126627772257399155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2081205472236565964727893 24389126627772257399155)
              ·
                rfl

theorem cell22_1923655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 8].length) (baseStart_1923655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923655 prefixEnd_1923655 := by exact prefixLift 1923655
  have htrace : WordTrace (prefixWord ++ tailWord_1923655) baseStart_1923655 baseEnd_1923655 := by
    simpa [prefixWord, tailWord_1923655, baseEnd_1923655] using wordTrace_append hprefix tailTrace_1923655
  have hstable : (prefixWord ++ tailWord_1923655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923655).length < 2 ^ (prefixWord ++ tailWord_1923655).sum := by decide
  have hdescent : baseEnd_1923655 < baseStart_1923655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923661 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1923661 : Nat := 118140960795 + 1923661 * 2 ^ 59
def prefixEnd_1923661 : Nat := 4983230072969 + 3 ^ 40 * 1923661 * 2
def baseEnd_1923661 : Nat := 219502824290822978042389

theorem tailTrace_1923661 : CollatzResearch.WordTrace tailWord_1923661 prefixEnd_1923661 219502824290822978042389 := by
  unfold tailWord_1923661
  simp only [CollatzResearch.WordTrace]
  refine ⟨70161680683912206987890837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46774453789274804658593891 70161680683912206987890837)
  ·
    refine ⟨3288828782058384702557383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70161680683912206987890837 3288828782058384702557383)
    ·
      refine ⟨4933243173087577053836075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288828782058384702557383 4933243173087577053836075)
      ·
        refine ⟨7399864759631365580754113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933243173087577053836075 7399864759631365580754113)
        ·
          refine ⟨5549898569723524185565585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7399864759631365580754113 5549898569723524185565585)
          ·
            refine ⟨4162423927292643139174189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549898569723524185565585 4162423927292643139174189)
            ·
              refine ⟨1560908972734741177190321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4162423927292643139174189 1560908972734741177190321)
              ·
                refine ⟨1170681729551055882892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560908972734741177190321 1170681729551055882892741)
                ·
                  refine ⟨219502824290822978042389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170681729551055882892741 219502824290822978042389)
                  ·
                    rfl

theorem cell22_1923661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1923661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923661 prefixEnd_1923661 := by exact prefixLift 1923661
  have htrace : WordTrace (prefixWord ++ tailWord_1923661) baseStart_1923661 baseEnd_1923661 := by
    simpa [prefixWord, tailWord_1923661, baseEnd_1923661] using wordTrace_append hprefix tailTrace_1923661
  have hstable : (prefixWord ++ tailWord_1923661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923661).length < 2 ^ (prefixWord ++ tailWord_1923661).sum := by decide
  have hdescent : baseEnd_1923661 < baseStart_1923661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923717 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 5]
def baseStart_1923717 : Nat := 118140960795 + 1923717 * 2 ^ 59
def prefixEnd_1923717 : Nat := 4983230072969 + 3 ^ 40 * 1923717 * 2
def baseEnd_1923717 : Nat := 219509214272301151575665

theorem tailTrace_1923717 : CollatzResearch.WordTrace tailWord_1923717 prefixEnd_1923717 219509214272301151575665 := by
  unfold tailWord_1923717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70163723171709328551929405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46775815447806219034619603 70163723171709328551929405)
  ·
    refine ⟨26311396189390998206973527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70163723171709328551929405 26311396189390998206973527)
    ·
      refine ⟨39467094284086497310460291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26311396189390998206973527 39467094284086497310460291)
      ·
        refine ⟨59200641426129745965690437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39467094284086497310460291 59200641426129745965690437)
        ·
          refine ⟨11100120267399327368566957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59200641426129745965690437 11100120267399327368566957)
          ·
            refine ⟨4162545100274747763212609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11100120267399327368566957 4162545100274747763212609)
            ·
              refine ⟨3121908825206060822409457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162545100274747763212609 3121908825206060822409457)
              ·
                refine ⟨2341431618904545616807093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121908825206060822409457 2341431618904545616807093)
                ·
                  refine ⟨219509214272301151575665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341431618904545616807093 219509214272301151575665)
                  ·
                    rfl

theorem cell22_1923717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_1923717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923717 prefixEnd_1923717 := by exact prefixLift 1923717
  have htrace : WordTrace (prefixWord ++ tailWord_1923717) baseStart_1923717 baseEnd_1923717 := by
    simpa [prefixWord, tailWord_1923717, baseEnd_1923717] using wordTrace_append hprefix tailTrace_1923717
  have hstable : (prefixWord ++ tailWord_1923717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923717).length < 2 ^ (prefixWord ++ tailWord_1923717).sum := by decide
  have hdescent : baseEnd_1923717 < baseStart_1923717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923732 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1923732 : Nat := 118140960795 + 1923732 * 2 ^ 59
def prefixEnd_1923732 : Nat := 4983230072969 + 3 ^ 40 * 1923732 * 2
def baseEnd_1923732 : Nat := 658532777623448415601949

theorem tailTrace_1923732 : CollatzResearch.WordTrace tailWord_1923732 prefixEnd_1923732 658532777623448415601949 := by
  unfold tailWord_1923732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082135133327493056862725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46776180177769990742483633 35082135133327493056862725)
  ·
    refine ⟨6577900337498904948161761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35082135133327493056862725 6577900337498904948161761)
    ·
      refine ⟨4933425253124178711121321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6577900337498904948161761 4933425253124178711121321)
      ·
        refine ⟨3700068939843134033340991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933425253124178711121321 3700068939843134033340991)
        ·
          refine ⟨5550103409764701050011487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700068939843134033340991 5550103409764701050011487)
          ·
            refine ⟨8325155114647051575017231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550103409764701050011487 8325155114647051575017231)
            ·
              refine ⟨12487732671970577362525847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325155114647051575017231 12487732671970577362525847)
              ·
                refine ⟨18731599007955866043788771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487732671970577362525847 18731599007955866043788771)
                ·
                  refine ⟨28097398511933799065683157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18731599007955866043788771 28097398511933799065683157)
                  ·
                    refine ⟨658532777623448415601949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28097398511933799065683157 658532777623448415601949)
                    ·
                      rfl

theorem cell22_1923732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1923732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923732 prefixEnd_1923732 := by exact prefixLift 1923732
  have htrace : WordTrace (prefixWord ++ tailWord_1923732) baseStart_1923732 baseEnd_1923732 := by
    simpa [prefixWord, tailWord_1923732, baseEnd_1923732] using wordTrace_append hprefix tailTrace_1923732
  have hstable : (prefixWord ++ tailWord_1923732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923732).length < 2 ^ (prefixWord ++ tailWord_1923732).sum := by decide
  have hdescent : baseEnd_1923732 < baseStart_1923732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923807 : List Nat := [1, 1, 2, 3, 2, 3, 4, 6]
def baseStart_1923807 : Nat := 118140960795 + 1923807 * 2 ^ 59
def prefixEnd_1923807 : Nat := 4983230072969 + 3 ^ 40 * 1923807 * 2
def baseEnd_1923807 : Nat := 73173161295130357775191

theorem tailTrace_1923807 : CollatzResearch.WordTrace tailWord_1923807 prefixEnd_1923807 73173161295130357775191 := by
  unfold tailWord_1923807
  simp only [CollatzResearch.WordTrace]
  refine ⟨70167005741383273922705675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46778003827588849281803783 70167005741383273922705675)
  ·
    refine ⟨105250508612074910884058513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70167005741383273922705675 105250508612074910884058513)
    ·
      refine ⟨78937881459056183163043885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105250508612074910884058513 78937881459056183163043885)
      ·
        refine ⟨29601705547146068686141457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78937881459056183163043885 29601705547146068686141457)
        ·
          refine ⟨22201279160359551514606093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29601705547146068686141457 22201279160359551514606093)
          ·
            refine ⟨8325479685134831817977285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22201279160359551514606093 8325479685134831817977285)
            ·
              refine ⟨1561027440962780965870741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8325479685134831817977285 1561027440962780965870741)
              ·
                refine ⟨73173161295130357775191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1561027440962780965870741 73173161295130357775191)
                ·
                  rfl

theorem cell22_1923807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 6].length) (baseStart_1923807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923807 prefixEnd_1923807 := by exact prefixLift 1923807
  have htrace : WordTrace (prefixWord ++ tailWord_1923807) baseStart_1923807 baseEnd_1923807 := by
    simpa [prefixWord, tailWord_1923807, baseEnd_1923807] using wordTrace_append hprefix tailTrace_1923807
  have hstable : (prefixWord ++ tailWord_1923807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923807).length < 2 ^ (prefixWord ++ tailWord_1923807).sum := by decide
  have hdescent : baseEnd_1923807 < baseStart_1923807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923820 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1923820 : Nat := 118140960795 + 1923820 * 2 ^ 59
def prefixEnd_1923820 : Nat := 4983230072969 + 3 ^ 40 * 1923820 * 2
def baseEnd_1923820 : Nat := 658562901821845519401679

theorem tailTrace_1923820 : CollatzResearch.WordTrace tailWord_1923820 prefixEnd_1923820 658562901821845519401679 := by
  unfold tailWord_1923820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35083739945168088571464457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46778319926890784761952609 35083739945168088571464457)
  ·
    refine ⟨26312804958876066428598343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35083739945168088571464457 26312804958876066428598343)
    ·
      refine ⟨39469207438314099642897515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26312804958876066428598343 39469207438314099642897515)
      ·
        refine ⟨59203811157471149464346273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39469207438314099642897515 59203811157471149464346273)
        ·
          refine ⟨44402858368103362098259705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59203811157471149464346273 44402858368103362098259705)
          ·
            refine ⟨33302143776077521573694779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44402858368103362098259705 33302143776077521573694779)
            ·
              refine ⟨49953215664116282360542169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33302143776077521573694779 49953215664116282360542169)
              ·
                refine ⟨37464911748087211770406627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49953215664116282360542169 37464911748087211770406627)
                ·
                  refine ⟨56197367622130817655609941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37464911748087211770406627 56197367622130817655609941)
                  ·
                    refine ⟨658562901821845519401679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56197367622130817655609941 658562901821845519401679)
                    ·
                      rfl

theorem cell22_1923820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1923820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923820 prefixEnd_1923820 := by exact prefixLift 1923820
  have htrace : WordTrace (prefixWord ++ tailWord_1923820) baseStart_1923820 baseEnd_1923820 := by
    simpa [prefixWord, tailWord_1923820, baseEnd_1923820] using wordTrace_append hprefix tailTrace_1923820
  have hstable : (prefixWord ++ tailWord_1923820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923820).length < 2 ^ (prefixWord ++ tailWord_1923820).sum := by decide
  have hdescent : baseEnd_1923820 < baseStart_1923820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923886 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1923886 : Nat := 118140960795 + 1923886 * 2 ^ 59
def prefixEnd_1923886 : Nat := 4983230072969 + 3 ^ 40 * 1923886 * 2
def baseEnd_1923886 : Nat := 219528498323547782417159

theorem tailTrace_1923886 : CollatzResearch.WordTrace tailWord_1923886 prefixEnd_1923886 219528498323547782417159 := by
  unfold tailWord_1923886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771235888512133801853939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46779924738731380276554341 8771235888512133801853939)
  ·
    refine ⟨13156853832768200702780909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771235888512133801853939 13156853832768200702780909)
    ·
      refine ⟨4933820187288075263542841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13156853832768200702780909 4933820187288075263542841)
      ·
        refine ⟨3700365140466056447657131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933820187288075263542841 3700365140466056447657131)
        ·
          refine ⟨5550547710699084671485697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700365140466056447657131 5550547710699084671485697)
          ·
            refine ⟨4162910783024313503614273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550547710699084671485697 4162910783024313503614273)
            ·
              refine ⟨3122183087268235127710705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162910783024313503614273 3122183087268235127710705)
              ·
                refine ⟨2341637315451176345783029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122183087268235127710705 2341637315451176345783029)
                ·
                  refine ⟨219528498323547782417159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341637315451176345783029 219528498323547782417159)
                  ·
                    rfl

theorem cell22_1923886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1923886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923886 prefixEnd_1923886 := by exact prefixLift 1923886
  have htrace : WordTrace (prefixWord ++ tailWord_1923886) baseStart_1923886 baseEnd_1923886 := by
    simpa [prefixWord, tailWord_1923886, baseEnd_1923886] using wordTrace_append hprefix tailTrace_1923886
  have hstable : (prefixWord ++ tailWord_1923886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923886).length < 2 ^ (prefixWord ++ tailWord_1923886).sum := by decide
  have hdescent : baseEnd_1923886 < baseStart_1923886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923976 : List Nat := [2, 1, 3, 3, 2, 3, 2, 6]
def baseStart_1923976 : Nat := 118140960795 + 1923976 * 2 ^ 59
def prefixEnd_1923976 : Nat := 4983230072969 + 3 ^ 40 * 1923976 * 2
def baseEnd_1923976 : Nat := 73179589312212568055689

theorem tailTrace_1923976 : CollatzResearch.WordTrace tailWord_1923976 prefixEnd_1923976 73179589312212568055689 := by
  unfold tailWord_1923976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086584838885507892803891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46782113118514010523738521 35086584838885507892803891)
  ·
    refine ⟨52629877258328261839205837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086584838885507892803891 52629877258328261839205837)
    ·
      refine ⟨19736203971873098189702189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52629877258328261839205837 19736203971873098189702189)
      ·
        refine ⟨7401076489452411821138321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19736203971873098189702189 7401076489452411821138321)
        ·
          refine ⟨5550807367089308865853741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7401076489452411821138321 5550807367089308865853741)
          ·
            refine ⟨2081552762658490824695153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5550807367089308865853741 2081552762658490824695153)
            ·
              refine ⟨1561164571993868118521365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081552762658490824695153 1561164571993868118521365)
              ·
                refine ⟨73179589312212568055689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1561164571993868118521365 73179589312212568055689)
                ·
                  rfl

theorem cell22_1923976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_1923976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1923976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1923976 prefixEnd_1923976 := by exact prefixLift 1923976
  have htrace : WordTrace (prefixWord ++ tailWord_1923976) baseStart_1923976 baseEnd_1923976 := by
    simpa [prefixWord, tailWord_1923976, baseEnd_1923976] using wordTrace_append hprefix tailTrace_1923976
  have hstable : (prefixWord ++ tailWord_1923976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923976).length < 2 ^ (prefixWord ++ tailWord_1923976).sum := by decide
  have hdescent : baseEnd_1923976 < baseStart_1923976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924004 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1924004 : Nat := 118140960795 + 1924004 * 2 ^ 59
def prefixEnd_1924004 : Nat := 4983230072969 + 3 ^ 40 * 1924004 * 2
def baseEnd_1924004 : Nat := 219541962927376790933705

theorem tailTrace_1924004 : CollatzResearch.WordTrace tailWord_1924004 prefixEnd_1924004 219541962927376790933705 := by
  unfold tailWord_1924004
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087095460834788283813533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46782793947779717711751377 35087095460834788283813533)
  ·
    refine ⟨13157660797813045606430075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35087095460834788283813533 13157660797813045606430075)
    ·
      refine ⟨19736491196719568409645113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13157660797813045606430075 19736491196719568409645113)
      ·
        refine ⟨14802368397539676307233835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19736491196719568409645113 14802368397539676307233835)
        ·
          refine ⟨22203552596309514460850753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14802368397539676307233835 22203552596309514460850753)
          ·
            refine ⟨16652664447232135845638065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22203552596309514460850753 16652664447232135845638065)
            ·
              refine ⟨12489498335424101884228549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652664447232135845638065 12489498335424101884228549)
              ·
                refine ⟨2341780937892019103292853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12489498335424101884228549 2341780937892019103292853)
                ·
                  refine ⟨219541962927376790933705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341780937892019103292853 219541962927376790933705)
                  ·
                    rfl

theorem cell22_1924004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1924004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924004 prefixEnd_1924004 := by exact prefixLift 1924004
  have htrace : WordTrace (prefixWord ++ tailWord_1924004) baseStart_1924004 baseEnd_1924004 := by
    simpa [prefixWord, tailWord_1924004, baseEnd_1924004] using wordTrace_append hprefix tailTrace_1924004
  have hstable : (prefixWord ++ tailWord_1924004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924004).length < 2 ^ (prefixWord ++ tailWord_1924004).sum := by decide
  have hdescent : baseEnd_1924004 < baseStart_1924004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924081 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1924081 : Nat := 118140960795 + 1924081 * 2 ^ 59
def prefixEnd_1924081 : Nat := 4983230072969 + 3 ^ 40 * 1924081 * 2
def baseEnd_1924081 : Nat := 658652247455727838625879

theorem tailTrace_1924081 : CollatzResearch.WordTrace tailWord_1924081 prefixEnd_1924081 658652247455727838625879 := by
  unfold tailWord_1924081
  simp only [CollatzResearch.WordTrace]
  refine ⟨70176999342390618718180097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46784666228260412478786731 70176999342390618718180097)
  ·
    refine ⟨52632749506792964038635073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70176999342390618718180097 52632749506792964038635073)
    ·
      refine ⟨39474562130094723028976305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52632749506792964038635073 39474562130094723028976305)
      ·
        refine ⟨29605921597571042271732229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39474562130094723028976305 29605921597571042271732229)
        ·
          refine ⟨5551110299544570425949793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29605921597571042271732229 5551110299544570425949793)
          ·
            refine ⟨4163332724658427819462345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551110299544570425949793 4163332724658427819462345)
            ·
              refine ⟨3122499543493820864596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163332724658427819462345 3122499543493820864596759)
              ·
                refine ⟨4683749315240731296895139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122499543493820864596759 4683749315240731296895139)
                ·
                  refine ⟨7025623972861096945342709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683749315240731296895139 7025623972861096945342709)
                  ·
                    refine ⟨658652247455727838625879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7025623972861096945342709 658652247455727838625879)
                    ·
                      rfl

theorem cell22_1924081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1924081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924081 prefixEnd_1924081 := by exact prefixLift 1924081
  have htrace : WordTrace (prefixWord ++ tailWord_1924081) baseStart_1924081 baseEnd_1924081 := by
    simpa [prefixWord, tailWord_1924081, baseEnd_1924081] using wordTrace_append hprefix tailTrace_1924081
  have hstable : (prefixWord ++ tailWord_1924081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924081).length < 2 ^ (prefixWord ++ tailWord_1924081).sum := by decide
  have hdescent : baseEnd_1924081 < baseStart_1924081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924154 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1924154 : Nat := 118140960795 + 1924154 * 2 ^ 59
def prefixEnd_1924154 : Nat := 4983230072969 + 3 ^ 40 * 1924154 * 2
def baseEnd_1924154 : Nat := 658677236847579981550655

theorem tailTrace_1924154 : CollatzResearch.WordTrace tailWord_1924154 prefixEnd_1924154 658677236847579981550655 := by
  unfold tailWord_1924154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17544915467781538046396879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46786441247417434790391677 17544915467781538046396879)
  ·
    refine ⟨26317373201672307069595319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17544915467781538046396879 26317373201672307069595319)
    ·
      refine ⟨39476059802508460604392979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317373201672307069595319 39476059802508460604392979)
      ·
        refine ⟨59214089703762690906589469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39476059802508460604392979 59214089703762690906589469)
        ·
          refine ⟨22205283638911009089971051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59214089703762690906589469 22205283638911009089971051)
          ·
            refine ⟨33307925458366513634956577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22205283638911009089971051 33307925458366513634956577)
            ·
              refine ⟨24980944093774885226217433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33307925458366513634956577 24980944093774885226217433)
              ·
                refine ⟨18735708070331163919663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24980944093774885226217433 18735708070331163919663075)
                ·
                  refine ⟨28103562105496745879494613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18735708070331163919663075 28103562105496745879494613)
                  ·
                    refine ⟨658677236847579981550655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28103562105496745879494613 658677236847579981550655)
                    ·
                      rfl

theorem cell22_1924154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1924154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924154 prefixEnd_1924154 := by exact prefixLift 1924154
  have htrace : WordTrace (prefixWord ++ tailWord_1924154) baseStart_1924154 baseEnd_1924154 := by
    simpa [prefixWord, tailWord_1924154, baseEnd_1924154] using wordTrace_append hprefix tailTrace_1924154
  have hstable : (prefixWord ++ tailWord_1924154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924154).length < 2 ^ (prefixWord ++ tailWord_1924154).sum := by decide
  have hdescent : baseEnd_1924154 < baseStart_1924154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924216 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_1924216 : Nat := 118140960795 + 1924216 * 2 ^ 59
def prefixEnd_1924216 : Nat := 4983230072969 + 3 ^ 40 * 1924216 * 2
def baseEnd_1924216 : Nat := 658698460714632486500465

theorem tailTrace_1924216 : CollatzResearch.WordTrace tailWord_1924216 prefixEnd_1924216 658698460714632486500465 := by
  unfold tailWord_1924216
  simp only [CollatzResearch.WordTrace]
  refine ⟨35090961598450768387172251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46787948797934357849563001 35090961598450768387172251)
  ·
    refine ⟨52636442397676152580758377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35090961598450768387172251 52636442397676152580758377)
    ·
      refine ⟨39477331798257114435568783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52636442397676152580758377 39477331798257114435568783)
      ·
        refine ⟨59215997697385671653353175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39477331798257114435568783 59215997697385671653353175)
        ·
          refine ⟨88823996546078507480029763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59215997697385671653353175 88823996546078507480029763)
          ·
            refine ⟨133235994819117761220044645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88823996546078507480029763 133235994819117761220044645)
            ·
              refine ⟨24981749028584580228758371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133235994819117761220044645 24981749028584580228758371)
              ·
                refine ⟨37472623542876870343137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24981749028584580228758371 37472623542876870343137557)
                ·
                  refine ⟨1756529228572353297334573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37472623542876870343137557 1756529228572353297334573)
                  ·
                    refine ⟨658698460714632486500465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756529228572353297334573 658698460714632486500465)
                    ·
                      rfl

theorem cell22_1924216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_1924216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924216 prefixEnd_1924216 := by exact prefixLift 1924216
  have htrace : WordTrace (prefixWord ++ tailWord_1924216) baseStart_1924216 baseEnd_1924216 := by
    simpa [prefixWord, tailWord_1924216, baseEnd_1924216] using wordTrace_append hprefix tailTrace_1924216
  have hstable : (prefixWord ++ tailWord_1924216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924216).length < 2 ^ (prefixWord ++ tailWord_1924216).sum := by decide
  have hdescent : baseEnd_1924216 < baseStart_1924216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924229 : List Nat := [1, 3, 1, 1, 16]
def baseStart_1924229 : Nat := 118140960795 + 1924229 * 2 ^ 59
def prefixEnd_1924229 : Nat := 4983230072969 + 3 ^ 40 * 1924229 * 2
def baseEnd_1924229 : Nat := 2710711567408661670475

theorem tailTrace_1924229 : CollatzResearch.WordTrace tailWord_1924229 prefixEnd_1924229 2710711567408661670475 := by
  unfold tailWord_1924229
  simp only [CollatzResearch.WordTrace]
  refine ⟨70182397345854439994567741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46788264897236293329711827 70182397345854439994567741)
  ·
    refine ⟨26318399004695414997962903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70182397345854439994567741 26318399004695414997962903)
    ·
      refine ⟨39477598507043122496944355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26318399004695414997962903 39477598507043122496944355)
      ·
        refine ⟨59216397760564683745416533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39477598507043122496944355 59216397760564683745416533)
        ·
          refine ⟨2710711567408661670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 59216397760564683745416533 2710711567408661670475)
          ·
            rfl

theorem cell22_1924229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 16].length) (baseStart_1924229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924229 prefixEnd_1924229 := by exact prefixLift 1924229
  have htrace : WordTrace (prefixWord ++ tailWord_1924229) baseStart_1924229 baseEnd_1924229 := by
    simpa [prefixWord, tailWord_1924229, baseEnd_1924229] using wordTrace_append hprefix tailTrace_1924229
  have hstable : (prefixWord ++ tailWord_1924229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924229).length < 2 ^ (prefixWord ++ tailWord_1924229).sum := by decide
  have hdescent : baseEnd_1924229 < baseStart_1924229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924233 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_1924233 : Nat := 118140960795 + 1924233 * 2 ^ 59
def prefixEnd_1924233 : Nat := 4983230072969 + 3 ^ 40 * 1924233 * 2
def baseEnd_1924233 : Nat := 658704280162050108825413

theorem tailTrace_1924233 : CollatzResearch.WordTrace tailWord_1924233 prefixEnd_1924233 658704280162050108825413 := by
  unfold tailWord_1924233
  simp only [CollatzResearch.WordTrace]
  refine ⟨70182543237839948677713353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46788362158559965785142235 70182543237839948677713353)
  ·
    refine ⟨52636907428379961508285015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70182543237839948677713353 52636907428379961508285015)
    ·
      refine ⟨78955361142569942262427523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52636907428379961508285015 78955361142569942262427523)
      ·
        refine ⟨118433041713854913393641285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78955361142569942262427523 118433041713854913393641285)
        ·
          refine ⟨22206195321347796261307741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118433041713854913393641285 22206195321347796261307741)
          ·
            refine ⟨8327323245505423597990403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22206195321347796261307741 8327323245505423597990403)
            ·
              refine ⟨12490984868258135396985605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327323245505423597990403 12490984868258135396985605)
              ·
                refine ⟨2342059662798400386934801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12490984868258135396985605 2342059662798400386934801)
                ·
                  refine ⟨1756544747098800290201101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342059662798400386934801 1756544747098800290201101)
                  ·
                    refine ⟨658704280162050108825413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756544747098800290201101 658704280162050108825413)
                    ·
                      rfl

theorem cell22_1924233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_1924233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924233 prefixEnd_1924233 := by exact prefixLift 1924233
  have htrace : WordTrace (prefixWord ++ tailWord_1924233) baseStart_1924233 baseEnd_1924233 := by
    simpa [prefixWord, tailWord_1924233, baseEnd_1924233] using wordTrace_append hprefix tailTrace_1924233
  have hstable : (prefixWord ++ tailWord_1924233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924233).length < 2 ^ (prefixWord ++ tailWord_1924233).sum := by decide
  have hdescent : baseEnd_1924233 < baseStart_1924233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924250 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1924250 : Nat := 118140960795 + 1924250 * 2 ^ 59
def prefixEnd_1924250 : Nat := 4983230072969 + 3 ^ 40 * 1924250 * 2
def baseEnd_1924250 : Nat := 658710099609467731150361

theorem tailTrace_1924250 : CollatzResearch.WordTrace tailWord_1924250 prefixEnd_1924250 658710099609467731150361 := by
  unfold tailWord_1924250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17545790819694590145270551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46788775519185573720721469 17545790819694590145270551)
  ·
    refine ⟨26318686229541885217905827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17545790819694590145270551 26318686229541885217905827)
    ·
      refine ⟨39478029344312827826858741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26318686229541885217905827 39478029344312827826858741)
      ·
        refine ⟨3701065251029327608768007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39478029344312827826858741 3701065251029327608768007)
        ·
          refine ⟨5551597876543991413152011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701065251029327608768007 5551597876543991413152011)
          ·
            refine ⟨8327396814815987119728017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551597876543991413152011 8327396814815987119728017)
            ·
              refine ⟨6245547611111990339796013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327396814815987119728017 6245547611111990339796013)
              ·
                refine ⟨2342080354166996377423505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6245547611111990339796013 2342080354166996377423505)
                ·
                  refine ⟨1756560265625247283067629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342080354166996377423505 1756560265625247283067629)
                  ·
                    refine ⟨658710099609467731150361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756560265625247283067629 658710099609467731150361)
                    ·
                      rfl

theorem cell22_1924250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1924250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924250 prefixEnd_1924250 := by exact prefixLift 1924250
  have htrace : WordTrace (prefixWord ++ tailWord_1924250) baseStart_1924250 baseEnd_1924250 := by
    simpa [prefixWord, tailWord_1924250, baseEnd_1924250] using wordTrace_append hprefix tailTrace_1924250
  have hstable : (prefixWord ++ tailWord_1924250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924250).length < 2 ^ (prefixWord ++ tailWord_1924250).sum := by decide
  have hdescent : baseEnd_1924250 < baseStart_1924250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924291 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 5]
def baseStart_1924291 : Nat := 118140960795 + 1924291 * 2 ^ 59
def prefixEnd_1924291 : Nat := 4983230072969 + 3 ^ 40 * 1924291 * 2
def baseEnd_1924291 : Nat := 219574711582452430291745

theorem tailTrace_1924291 : CollatzResearch.WordTrace tailWord_1924291 prefixEnd_1924291 219574711582452430291745 := by
  unfold tailWord_1924291
  simp only [CollatzResearch.WordTrace]
  refine ⟨70184658671629824583324727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46789772447753216388883151 70184658671629824583324727)
  ·
    refine ⟨105276988007444736874987091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70184658671629824583324727 105276988007444736874987091)
    ·
      refine ⟨157915482011167105312480637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105276988007444736874987091 157915482011167105312480637)
      ·
        refine ⟨59218305754187664492180239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157915482011167105312480637 59218305754187664492180239)
        ·
          refine ⟨88827458631281496738270359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59218305754187664492180239 88827458631281496738270359)
          ·
            refine ⟨133241187946922245107405539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88827458631281496738270359 133241187946922245107405539)
            ·
              refine ⟨199861781920383367661108309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133241187946922245107405539 199861781920383367661108309)
              ·
                refine ⟨2342130256879492589778613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 199861781920383367661108309 2342130256879492589778613)
                ·
                  refine ⟨219574711582452430291745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342130256879492589778613 219574711582452430291745)
                  ·
                    rfl

theorem cell22_1924291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 5].length) (baseStart_1924291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924291 prefixEnd_1924291 := by exact prefixLift 1924291
  have htrace : WordTrace (prefixWord ++ tailWord_1924291) baseStart_1924291 baseEnd_1924291 := by
    simpa [prefixWord, tailWord_1924291, baseEnd_1924291] using wordTrace_append hprefix tailTrace_1924291
  have hstable : (prefixWord ++ tailWord_1924291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924291).length < 2 ^ (prefixWord ++ tailWord_1924291).sum := by decide
  have hdescent : baseEnd_1924291 < baseStart_1924291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924301 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1924301 : Nat := 118140960795 + 1924301 * 2 ^ 59
def prefixEnd_1924301 : Nat := 4983230072969 + 3 ^ 40 * 1924301 * 2
def baseEnd_1924301 : Nat := 658727557951720598125205

theorem tailTrace_1924301 : CollatzResearch.WordTrace tailWord_1924301 prefixEnd_1924301 658727557951720598125205 := by
  unfold tailWord_1924301
  simp only [CollatzResearch.WordTrace]
  refine ⟨70185023401593596291188757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46790015601062397527459171 70185023401593596291188757)
  ·
    refine ⟨3289922971949699826149473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70185023401593596291188757 3289922971949699826149473)
    ·
      refine ⟨2467442228962274869612105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3289922971949699826149473 2467442228962274869612105)
      ·
        refine ⟨1850581671721706152209079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2467442228962274869612105 1850581671721706152209079)
        ·
          refine ⟨2775872507582559228313619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850581671721706152209079 2775872507582559228313619)
          ·
            refine ⟨4163808761373838842470429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775872507582559228313619 4163808761373838842470429)
            ·
              refine ⟨1561428285515189565926411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4163808761373838842470429 1561428285515189565926411)
              ·
                refine ⟨2342142428272784348889617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561428285515189565926411 2342142428272784348889617)
                ·
                  refine ⟨1756606821204588261667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342142428272784348889617 1756606821204588261667213)
                  ·
                    refine ⟨658727557951720598125205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756606821204588261667213 658727557951720598125205)
                    ·
                      rfl

theorem cell22_1924301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1924301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924301 prefixEnd_1924301 := by exact prefixLift 1924301
  have htrace : WordTrace (prefixWord ++ tailWord_1924301) baseStart_1924301 baseEnd_1924301 := by
    simpa [prefixWord, tailWord_1924301, baseEnd_1924301] using wordTrace_append hprefix tailTrace_1924301
  have hstable : (prefixWord ++ tailWord_1924301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924301).length < 2 ^ (prefixWord ++ tailWord_1924301).sum := by decide
  have hdescent : baseEnd_1924301 < baseStart_1924301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924353 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 6]
def baseStart_1924353 : Nat := 118140960795 + 1924353 * 2 ^ 59
def prefixEnd_1924353 : Nat := 4983230072969 + 3 ^ 40 * 1924353 * 2
def baseEnd_1924353 : Nat := 219581786204803265275015

theorem tailTrace_1924353 : CollatzResearch.WordTrace tailWord_1924353 prefixEnd_1924353 219581786204803265275015 := by
  unfold tailWord_1924353
  simp only [CollatzResearch.WordTrace]
  refine ⟨70186919997405209172081713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46791279998270139448054475 70186919997405209172081713)
  ·
    refine ⟨52640189998053906879061285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70186919997405209172081713 52640189998053906879061285)
    ·
      refine ⟨9870035624635107539823991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52640189998053906879061285 9870035624635107539823991)
      ·
        refine ⟨14805053436952661309735987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9870035624635107539823991 14805053436952661309735987)
        ·
          refine ⟨22207580155428991964603981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14805053436952661309735987 22207580155428991964603981)
          ·
            refine ⟨8327842558285871986726493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22207580155428991964603981 8327842558285871986726493)
            ·
              refine ⟨3122940959357201995022435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8327842558285871986726493 3122940959357201995022435)
              ·
                refine ⟨4684411439035802992533653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122940959357201995022435 4684411439035802992533653)
                ·
                  refine ⟨219581786204803265275015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4684411439035802992533653 219581786204803265275015)
                  ·
                    rfl

theorem cell22_1924353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_1924353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924353 prefixEnd_1924353 := by exact prefixLift 1924353
  have htrace : WordTrace (prefixWord ++ tailWord_1924353) baseStart_1924353 baseEnd_1924353 := by
    simpa [prefixWord, tailWord_1924353, baseEnd_1924353] using wordTrace_append hprefix tailTrace_1924353
  have hstable : (prefixWord ++ tailWord_1924353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924353).length < 2 ^ (prefixWord ++ tailWord_1924353).sum := by decide
  have hdescent : baseEnd_1924353 < baseStart_1924353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924402 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1924402 : Nat := 118140960795 + 1924402 * 2 ^ 59
def prefixEnd_1924402 : Nat := 4983230072969 + 3 ^ 40 * 1924402 * 2
def baseEnd_1924402 : Nat := 658762132315790001349895

theorem tailTrace_1924402 : CollatzResearch.WordTrace tailWord_1924402 prefixEnd_1924402 658762132315790001349895 := by
  unfold tailWord_1924402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547176793556922635153865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46792471449485127027076973 17547176793556922635153865)
  ·
    refine ⟨13160382595167691976365399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17547176793556922635153865 13160382595167691976365399)
    ·
      refine ⟨19740573892751537964548099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13160382595167691976365399 19740573892751537964548099)
      ·
        refine ⟨29610860839127306946822149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19740573892751537964548099 29610860839127306946822149)
        ·
          refine ⟨5552036407336370052529153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29610860839127306946822149 5552036407336370052529153)
          ·
            refine ⟨4164027305502277539396865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552036407336370052529153 4164027305502277539396865)
            ·
              refine ⟨3123020479126708154547649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164027305502277539396865 3123020479126708154547649)
              ·
                refine ⟨2342265359345031115910737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123020479126708154547649 2342265359345031115910737)
                ·
                  refine ⟨1756699019508773336933053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342265359345031115910737 1756699019508773336933053)
                  ·
                    refine ⟨658762132315790001349895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756699019508773336933053 658762132315790001349895)
                    ·
                      rfl

theorem cell22_1924402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1924402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924402 prefixEnd_1924402 := by exact prefixLift 1924402
  have htrace : WordTrace (prefixWord ++ tailWord_1924402) baseStart_1924402 baseEnd_1924402 := by
    simpa [prefixWord, tailWord_1924402, baseEnd_1924402] using wordTrace_append hprefix tailTrace_1924402
  have hstable : (prefixWord ++ tailWord_1924402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924402).length < 2 ^ (prefixWord ++ tailWord_1924402).sum := by decide
  have hdescent : baseEnd_1924402 < baseStart_1924402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924430 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1924430 : Nat := 118140960795 + 1924430 * 2 ^ 59
def prefixEnd_1924430 : Nat := 4983230072969 + 3 ^ 40 * 1924430 * 2
def baseEnd_1924430 : Nat := 658771717288007261649809

theorem tailTrace_1924430 : CollatzResearch.WordTrace tailWord_1924430 prefixEnd_1924430 658771717288007261649809 := by
  unfold tailWord_1924430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773716052265781415329343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46793152278750834215089829 8773716052265781415329343)
  ·
    refine ⟨13160574078398672122994015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8773716052265781415329343 13160574078398672122994015)
    ·
      refine ⟨19740861117598008184491023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13160574078398672122994015 19740861117598008184491023)
      ·
        refine ⟨29611291676397012276736535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19740861117598008184491023 29611291676397012276736535)
        ·
          refine ⟨44416937514595518415104803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29611291676397012276736535 44416937514595518415104803)
          ·
            refine ⟨66625406271893277622657205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44416937514595518415104803 66625406271893277622657205)
            ·
              refine ⟨6246131837989994777124113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66625406271893277622657205 6246131837989994777124113)
              ·
                refine ⟨4684598878492496082843085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246131837989994777124113 4684598878492496082843085)
                ·
                  refine ⟨1756724579434686031066157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4684598878492496082843085 1756724579434686031066157)
                  ·
                    refine ⟨658771717288007261649809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756724579434686031066157 658771717288007261649809)
                    ·
                      rfl

theorem cell22_1924430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1924430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924430 prefixEnd_1924430 := by exact prefixLift 1924430
  have htrace : WordTrace (prefixWord ++ tailWord_1924430) baseStart_1924430 baseEnd_1924430 := by
    simpa [prefixWord, tailWord_1924430, baseEnd_1924430] using wordTrace_append hprefix tailTrace_1924430
  have hstable : (prefixWord ++ tailWord_1924430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924430).length < 2 ^ (prefixWord ++ tailWord_1924430).sum := by decide
  have hdescent : baseEnd_1924430 < baseStart_1924430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924438 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1924438 : Nat := 118140960795 + 1924438 * 2 ^ 59
def prefixEnd_1924438 : Nat := 4983230072969 + 3 ^ 40 * 1924438 * 2
def baseEnd_1924438 : Nat := 219591485283832635816595

theorem tailTrace_1924438 : CollatzResearch.WordTrace tailWord_1924438 prefixEnd_1924438 219591485283832635816595 := by
  unfold tailWord_1924438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386876262631079293057873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46793346801398179125950645 4386876262631079293057873)
  ·
    refine ⟨3290157196973309469793405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4386876262631079293057873 3290157196973309469793405)
    ·
      refine ⟨1233808948864991051172527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3290157196973309469793405 1233808948864991051172527)
      ·
        refine ⟨1850713423297486576758791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233808948864991051172527 1850713423297486576758791)
        ·
          refine ⟨2776070134946229865138187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850713423297486576758791 2776070134946229865138187)
          ·
            refine ⟨4164105202419344797707281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776070134946229865138187 4164105202419344797707281)
            ·
              refine ⟨3123078901814508598280461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164105202419344797707281 3123078901814508598280461)
              ·
                refine ⟨1171154588180440724355173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123078901814508598280461 1171154588180440724355173)
                ·
                  refine ⟨219591485283832635816595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171154588180440724355173 219591485283832635816595)
                  ·
                    rfl

theorem cell22_1924438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1924438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924438 prefixEnd_1924438 := by exact prefixLift 1924438
  have htrace : WordTrace (prefixWord ++ tailWord_1924438) baseStart_1924438 baseEnd_1924438 := by
    simpa [prefixWord, tailWord_1924438, baseEnd_1924438] using wordTrace_append hprefix tailTrace_1924438
  have hstable : (prefixWord ++ tailWord_1924438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924438).length < 2 ^ (prefixWord ++ tailWord_1924438).sum := by decide
  have hdescent : baseEnd_1924438 < baseStart_1924438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924460 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1924460 : Nat := 118140960795 + 1924460 * 2 ^ 59
def prefixEnd_1924460 : Nat := 4983230072969 + 3 ^ 40 * 1924460 * 2
def baseEnd_1924460 : Nat := 219593995633699061133239

theorem tailTrace_1924460 : CollatzResearch.WordTrace tailWord_1924460 prefixEnd_1924460 219593995633699061133239 := by
  unfold tailWord_1924460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095411304008783223113417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46793881738678377630817889 35095411304008783223113417)
  ·
    refine ⟨26321558478006587417335063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35095411304008783223113417 26321558478006587417335063)
    ·
      refine ⟨39482337717009881126002595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26321558478006587417335063 39482337717009881126002595)
      ·
        refine ⟨59223506575514821689003893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39482337717009881126002595 59223506575514821689003893)
        ·
          refine ⟨5552203741454514533344115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59223506575514821689003893 5552203741454514533344115)
          ·
            refine ⟨8328305612181771800016173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552203741454514533344115 8328305612181771800016173)
            ·
              refine ⟨3123114604568164425006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8328305612181771800016173 3123114604568164425006065)
              ·
                refine ⟨2342335953426123318754549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123114604568164425006065 2342335953426123318754549)
                ·
                  refine ⟨219593995633699061133239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342335953426123318754549 219593995633699061133239)
                  ·
                    rfl

theorem cell22_1924460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1924460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924460 prefixEnd_1924460 := by exact prefixLift 1924460
  have htrace : WordTrace (prefixWord ++ tailWord_1924460) baseStart_1924460 baseEnd_1924460 := by
    simpa [prefixWord, tailWord_1924460, baseEnd_1924460] using wordTrace_append hprefix tailTrace_1924460
  have hstable : (prefixWord ++ tailWord_1924460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924460).length < 2 ^ (prefixWord ++ tailWord_1924460).sum := by decide
  have hdescent : baseEnd_1924460 < baseStart_1924460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924473 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_1924473 : Nat := 118140960795 + 1924473 * 2 ^ 59
def prefixEnd_1924473 : Nat := 4983230072969 + 3 ^ 40 * 1924473 * 2
def baseEnd_1924473 : Nat := 658786437066769482824677

theorem tailTrace_1924473 : CollatzResearch.WordTrace tailWord_1924473 prefixEnd_1924473 658786437066769482824677 := by
  unfold tailWord_1924473
  simp only [CollatzResearch.WordTrace]
  refine ⟨70191296756970469666450073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46794197837980313110966715 70191296756970469666450073)
  ·
    refine ⟨52643472567727852249837555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70191296756970469666450073 52643472567727852249837555)
    ·
      refine ⟨78965208851591778374756333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52643472567727852249837555 78965208851591778374756333)
      ·
        refine ⟨29611953319346916890533625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78965208851591778374756333 29611953319346916890533625)
        ·
          refine ⟨22208964989510187667900219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29611953319346916890533625 22208964989510187667900219)
          ·
            refine ⟨33313447484265281501850329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22208964989510187667900219 33313447484265281501850329)
            ·
              refine ⟨24985085613198961126387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33313447484265281501850329 24985085613198961126387747)
              ·
                refine ⟨37477628419798441689581621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24985085613198961126387747 37477628419798441689581621)
                ·
                  refine ⟨3513527664356103908398277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37477628419798441689581621 3513527664356103908398277)
                  ·
                    refine ⟨658786437066769482824677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3513527664356103908398277 658786437066769482824677)
                    ·
                      rfl

theorem cell22_1924473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_1924473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924473 prefixEnd_1924473 := by exact prefixLift 1924473
  have htrace : WordTrace (prefixWord ++ tailWord_1924473) baseStart_1924473 baseEnd_1924473 := by
    simpa [prefixWord, tailWord_1924473, baseEnd_1924473] using wordTrace_append hprefix tailTrace_1924473
  have hstable : (prefixWord ++ tailWord_1924473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924473).length < 2 ^ (prefixWord ++ tailWord_1924473).sum := by decide
  have hdescent : baseEnd_1924473 < baseStart_1924473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924498 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1924498 : Nat := 118140960795 + 1924498 * 2 ^ 59
def prefixEnd_1924498 : Nat := 4983230072969 + 3 ^ 40 * 1924498 * 2
def baseEnd_1924498 : Nat := 658794995077677750949601

theorem tailTrace_1924498 : CollatzResearch.WordTrace tailWord_1924498 prefixEnd_1924498 658794995077677750949601 := by
  unfold tailWord_1924498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548052145469974734027537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46794805721253265957406765 17548052145469974734027537)
  ·
    refine ⟨13161039109102481050520653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17548052145469974734027537 13161039109102481050520653)
    ·
      refine ⟨4935389665913430393945245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13161039109102481050520653 4935389665913430393945245)
      ·
        refine ⟨1850771124717536397729467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4935389665913430393945245 1850771124717536397729467)
        ·
          refine ⟨2776156687076304596594201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850771124717536397729467 2776156687076304596594201)
          ·
            refine ⟨2082117515307228447445651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776156687076304596594201 2082117515307228447445651)
            ·
              refine ⟨3123176272960842671168477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082117515307228447445651 3123176272960842671168477)
              ·
                refine ⟨1171191102360316001688179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123176272960842671168477 1171191102360316001688179)
                ·
                  refine ⟨1756786653540474002532269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171191102360316001688179 1756786653540474002532269)
                  ·
                    refine ⟨658794995077677750949601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756786653540474002532269 658794995077677750949601)
                    ·
                      rfl

theorem cell22_1924498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1924498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924498 prefixEnd_1924498 := by exact prefixLift 1924498
  have htrace : WordTrace (prefixWord ++ tailWord_1924498) baseStart_1924498 baseEnd_1924498 := by
    simpa [prefixWord, tailWord_1924498, baseEnd_1924498] using wordTrace_append hprefix tailTrace_1924498
  have hstable : (prefixWord ++ tailWord_1924498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924498).length < 2 ^ (prefixWord ++ tailWord_1924498).sum := by decide
  have hdescent : baseEnd_1924498 < baseStart_1924498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924503 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1924503 : Nat := 118140960795 + 1924503 * 2 ^ 59
def prefixEnd_1924503 : Nat := 4983230072969 + 3 ^ 40 * 1924503 * 2
def baseEnd_1924503 : Nat := 658796706679859404574585

theorem tailTrace_1924503 : CollatzResearch.WordTrace tailWord_1924503 prefixEnd_1924503 658796706679859404574585 := by
  unfold tailWord_1924503
  simp only [CollatzResearch.WordTrace]
  refine ⟨70192390946861784790042163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46794927297907856526694775 70192390946861784790042163)
  ·
    refine ⟨105288586420292677185063245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70192390946861784790042163 105288586420292677185063245)
    ·
      refine ⟨39483219907609753944398717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105288586420292677185063245 39483219907609753944398717)
      ·
        refine ⟨14806207465353657729149519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39483219907609753944398717 14806207465353657729149519)
        ·
          refine ⟨22209311198030486593724279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14806207465353657729149519 22209311198030486593724279)
          ·
            refine ⟨33313966797045729890586419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22209311198030486593724279 33313966797045729890586419)
            ·
              refine ⟨49970950195568594835879629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33313966797045729890586419 49970950195568594835879629)
              ·
                refine ⟨18739106323338223063454861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49970950195568594835879629 18739106323338223063454861)
                ·
                  refine ⟨7027164871251833648795573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18739106323338223063454861 7027164871251833648795573)
                  ·
                    refine ⟨658796706679859404574585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7027164871251833648795573 658796706679859404574585)
                    ·
                      rfl

theorem cell22_1924503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1924503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924503 prefixEnd_1924503 := by exact prefixLift 1924503
  have htrace : WordTrace (prefixWord ++ tailWord_1924503) baseStart_1924503 baseEnd_1924503 := by
    simpa [prefixWord, tailWord_1924503, baseEnd_1924503] using wordTrace_append hprefix tailTrace_1924503
  have hstable : (prefixWord ++ tailWord_1924503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924503).length < 2 ^ (prefixWord ++ tailWord_1924503).sum := by decide
  have hdescent : baseEnd_1924503 < baseStart_1924503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924730 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1924730 : Nat := 118140960795 + 1924730 * 2 ^ 59
def prefixEnd_1924730 : Nat := 4983230072969 + 3 ^ 40 * 1924730 * 2
def baseEnd_1924730 : Nat := 219624804472968826382963

theorem tailTrace_1924730 : CollatzResearch.WordTrace tailWord_1924730 prefixEnd_1924730 219624804472968826382963 := by
  unfold tailWord_1924730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550167579259850639638911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46800446878026268372370429 17550167579259850639638911)
  ·
    refine ⟨26325251368889775959458367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17550167579259850639638911 26325251368889775959458367)
    ·
      refine ⟨39487877053334663939187551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26325251368889775959458367 39487877053334663939187551)
      ·
        refine ⟨59231815580001995908781327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39487877053334663939187551 59231815580001995908781327)
        ·
          refine ⟨88847723370002993863171991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59231815580001995908781327 88847723370002993863171991)
          ·
            refine ⟨133271585055004490794757987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88847723370002993863171991 133271585055004490794757987)
            ·
              refine ⟨199907377582506736192136981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133271585055004490794757987 199907377582506736192136981)
              ·
                refine ⟨9370658324180003259006421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199907377582506736192136981 9370658324180003259006421)
                ·
                  refine ⟨219624804472968826382963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9370658324180003259006421 219624804472968826382963)
                  ·
                    rfl

theorem cell22_1924730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1924730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924730 prefixEnd_1924730 := by exact prefixLift 1924730
  have htrace : WordTrace (prefixWord ++ tailWord_1924730) baseStart_1924730 baseEnd_1924730 := by
    simpa [prefixWord, tailWord_1924730, baseEnd_1924730] using wordTrace_append hprefix tailTrace_1924730
  have hstable : (prefixWord ++ tailWord_1924730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924730).length < 2 ^ (prefixWord ++ tailWord_1924730).sum := by decide
  have hdescent : baseEnd_1924730 < baseStart_1924730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924747 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 5]
def baseStart_1924747 : Nat := 118140960795 + 1924747 * 2 ^ 59
def prefixEnd_1924747 : Nat := 4983230072969 + 3 ^ 40 * 1924747 * 2
def baseEnd_1924747 : Nat := 219626744288774700491279

theorem tailTrace_1924747 : CollatzResearch.WordTrace tailWord_1924747 prefixEnd_1924747 219626744288774700491279 := by
  unfold tailWord_1924747
  simp only [CollatzResearch.WordTrace]
  refine ⟨70201290357977814461924495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46800860238651876307949663 70201290357977814461924495)
  ·
    refine ⟨105301935536966721692886743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70201290357977814461924495 105301935536966721692886743)
    ·
      refine ⟨157952903305450082539330115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105301935536966721692886743 157952903305450082539330115)
      ·
        refine ⟨236929354958175123808995173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157952903305450082539330115 236929354958175123808995173)
        ·
          refine ⟨44424254054657835714186595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236929354958175123808995173 44424254054657835714186595)
          ·
            refine ⟨66636381081986753571279893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44424254054657835714186595 66636381081986753571279893)
            ·
              refine ⟨3123580363218129073653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66636381081986753571279893 3123580363218129073653745)
              ·
                refine ⟨2342685272413596805240309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123580363218129073653745 2342685272413596805240309)
                ·
                  refine ⟨219626744288774700491279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342685272413596805240309 219626744288774700491279)
                  ·
                    rfl

theorem cell22_1924747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 5].length) (baseStart_1924747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924747 prefixEnd_1924747 := by exact prefixLift 1924747
  have htrace : WordTrace (prefixWord ++ tailWord_1924747) baseStart_1924747 baseEnd_1924747 := by
    simpa [prefixWord, tailWord_1924747, baseEnd_1924747] using wordTrace_append hprefix tailTrace_1924747
  have hstable : (prefixWord ++ tailWord_1924747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924747).length < 2 ^ (prefixWord ++ tailWord_1924747).sum := by decide
  have hdescent : baseEnd_1924747 < baseStart_1924747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924794 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1924794 : Nat := 118140960795 + 1924794 * 2 ^ 59
def prefixEnd_1924794 : Nat := 4983230072969 + 3 ^ 40 * 1924794 * 2
def baseEnd_1924794 : Nat := 658896321926831645548693

theorem tailTrace_1924794 : CollatzResearch.WordTrace tailWord_1924794 prefixEnd_1924794 658896321926831645548693 := by
  unfold tailWord_1924794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550751147201885372221359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46802003059205027659256957 17550751147201885372221359)
  ·
    refine ⟨26326126720802828058332039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17550751147201885372221359 26326126720802828058332039)
    ·
      refine ⟨39489190081204242087498059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326126720802828058332039 39489190081204242087498059)
      ·
        refine ⟨59233785121806363131247089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39489190081204242087498059 59233785121806363131247089)
        ·
          refine ⟨44425338841354772348435317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59233785121806363131247089 44425338841354772348435317)
          ·
            refine ⟨4164875516377009907665811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44425338841354772348435317 4164875516377009907665811)
            ·
              refine ⟨6247313274565514861498717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164875516377009907665811 6247313274565514861498717)
              ·
                refine ⟨2342742477962068073062019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247313274565514861498717 2342742477962068073062019)
                ·
                  refine ⟨3514113716943102109593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342742477962068073062019 3514113716943102109593029)
                  ·
                    refine ⟨658896321926831645548693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3514113716943102109593029 658896321926831645548693)
                    ·
                      rfl

theorem cell22_1924794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1924794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924794 prefixEnd_1924794 := by exact prefixLift 1924794
  have htrace : WordTrace (prefixWord ++ tailWord_1924794) baseStart_1924794 baseEnd_1924794 := by
    simpa [prefixWord, tailWord_1924794, baseEnd_1924794] using wordTrace_append hprefix tailTrace_1924794
  have hstable : (prefixWord ++ tailWord_1924794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924794).length < 2 ^ (prefixWord ++ tailWord_1924794).sum := by decide
  have hdescent : baseEnd_1924794 < baseStart_1924794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924828 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1924828 : Nat := 118140960795 + 1924828 * 2 ^ 59
def prefixEnd_1924828 : Nat := 4983230072969 + 3 ^ 40 * 1924828 * 2
def baseEnd_1924828 : Nat := 658907960821666890198589

theorem tailTrace_1924828 : CollatzResearch.WordTrace tailWord_1924828 prefixEnd_1924828 658907960821666890198589 := by
  unfold tailWord_1924828
  simp only [CollatzResearch.WordTrace]
  refine ⟨35102122335342182647811569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46802829780456243530415425 35102122335342182647811569)
  ·
    refine ⟨26326591751506636985858677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35102122335342182647811569 26326591751506636985858677)
    ·
      refine ⟨2468117976703747217424251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26326591751506636985858677 2468117976703747217424251)
      ·
        refine ⟨3702176965055620826136377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468117976703747217424251 3702176965055620826136377)
        ·
          refine ⟨2776632723791715619602283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702176965055620826136377 2776632723791715619602283)
          ·
            refine ⟨4164949085687573429403425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776632723791715619602283 4164949085687573429403425)
            ·
              refine ⟨3123711814265680072052569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164949085687573429403425 3123711814265680072052569)
              ·
                refine ⟨2342783860699260054039427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123711814265680072052569 2342783860699260054039427)
                ·
                  refine ⟨3514175791048890081059141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342783860699260054039427 3514175791048890081059141)
                  ·
                    refine ⟨658907960821666890198589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3514175791048890081059141 658907960821666890198589)
                    ·
                      rfl

theorem cell22_1924828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1924828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924828 prefixEnd_1924828 := by exact prefixLift 1924828
  have htrace : WordTrace (prefixWord ++ tailWord_1924828) baseStart_1924828 baseEnd_1924828 := by
    simpa [prefixWord, tailWord_1924828, baseEnd_1924828] using wordTrace_append hprefix tailTrace_1924828
  have hstable : (prefixWord ++ tailWord_1924828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924828).length < 2 ^ (prefixWord ++ tailWord_1924828).sum := by decide
  have hdescent : baseEnd_1924828 < baseStart_1924828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924837 : List Nat := [1, 3, 1, 4, 1, 1, 3, 8]
def baseStart_1924837 : Nat := 118140960795 + 1924837 * 2 ^ 59
def prefixEnd_1924837 : Nat := 4983230072969 + 3 ^ 40 * 1924837 * 2
def baseEnd_1924837 : Nat := 73212337967288207413729

theorem tailTrace_1924837 : CollatzResearch.WordTrace tailWord_1924837 prefixEnd_1924837 73212337967288207413729 := by
  unfold tailWord_1924837
  simp only [CollatzResearch.WordTrace]
  refine ⟨70204572927651759832700765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46803048618434506555133843 70204572927651759832700765)
  ·
    refine ⟨26326714847869409937262787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70204572927651759832700765 26326714847869409937262787)
    ·
      refine ⟨39490072271804114905894181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326714847869409937262787 39490072271804114905894181)
      ·
        refine ⟨7404388550963271544855159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39490072271804114905894181 7404388550963271544855159)
        ·
          refine ⟨11106582826444907317282739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404388550963271544855159 11106582826444907317282739)
          ·
            refine ⟨16659874239667360975924109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106582826444907317282739 16659874239667360975924109)
            ·
              refine ⟨6247452839875260365971541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16659874239667360975924109 6247452839875260365971541)
              ·
                refine ⟨73212337967288207413729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6247452839875260365971541 73212337967288207413729)
                ·
                  rfl

theorem cell22_1924837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 8].length) (baseStart_1924837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924837 prefixEnd_1924837 := by exact prefixLift 1924837
  have htrace : WordTrace (prefixWord ++ tailWord_1924837) baseStart_1924837 baseEnd_1924837 := by
    simpa [prefixWord, tailWord_1924837, baseEnd_1924837] using wordTrace_append hprefix tailTrace_1924837
  have hstable : (prefixWord ++ tailWord_1924837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924837).length < 2 ^ (prefixWord ++ tailWord_1924837).sum := by decide
  have hdescent : baseEnd_1924837 < baseStart_1924837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924854 : List Nat := [5, 1, 1, 1, 1, 5, 8]
def baseStart_1924854 : Nat := 118140960795 + 1924854 * 2 ^ 59
def prefixEnd_1924854 : Nat := 4983230072969 + 3 ^ 40 * 1924854 * 2
def baseEnd_1924854 : Nat := 24404328190852277372167

theorem tailTrace_1924854 : CollatzResearch.WordTrace tailWord_1924854 prefixEnd_1924854 24404328190852277372167 := by
  unfold tailWord_1924854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387824560536885733504351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46803461979060114490713077 4387824560536885733504351)
  ·
    refine ⟨6581736840805328600256527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4387824560536885733504351 6581736840805328600256527)
    ·
      refine ⟨9872605261207992900384791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581736840805328600256527 9872605261207992900384791)
      ·
        refine ⟨14808907891811989350577187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9872605261207992900384791 14808907891811989350577187)
        ·
          refine ⟨22213361837717984025865781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14808907891811989350577187 22213361837717984025865781)
          ·
            refine ⟨2082502672286061002424917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22213361837717984025865781 2082502672286061002424917)
            ·
              refine ⟨24404328190852277372167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2082502672286061002424917 24404328190852277372167)
              ·
                rfl

theorem cell22_1924854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 8].length) (baseStart_1924854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924854 prefixEnd_1924854 := by exact prefixLift 1924854
  have htrace : WordTrace (prefixWord ++ tailWord_1924854) baseStart_1924854 baseEnd_1924854 := by
    simpa [prefixWord, tailWord_1924854, baseEnd_1924854] using wordTrace_append hprefix tailTrace_1924854
  have hstable : (prefixWord ++ tailWord_1924854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924854).length < 2 ^ (prefixWord ++ tailWord_1924854).sum := by decide
  have hdescent : baseEnd_1924854 < baseStart_1924854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924916 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1924916 : Nat := 118140960795 + 1924916 * 2 ^ 59
def prefixEnd_1924916 : Nat := 4983230072969 + 3 ^ 40 * 1924916 * 2
def baseEnd_1924916 : Nat := 219646028340021331332773

theorem tailTrace_1924916 : CollatzResearch.WordTrace tailWord_1924916 prefixEnd_1924916 219646028340021331332773 := by
  unfold tailWord_1924916
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103727147182778162413301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46804969529577037549884401 35103727147182778162413301)
  ·
    refine ⟨3290974420048385452726247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35103727147182778162413301 3290974420048385452726247)
    ·
      refine ⟨4936461630072578179089371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290974420048385452726247 4936461630072578179089371)
      ·
        refine ⟨7404692445108867268634057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936461630072578179089371 7404692445108867268634057)
        ·
          refine ⟨5553519333831650451475543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7404692445108867268634057 5553519333831650451475543)
          ·
            refine ⟨8330279000747475677213315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553519333831650451475543 8330279000747475677213315)
            ·
              refine ⟨12495418501121213515819973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330279000747475677213315 12495418501121213515819973)
              ·
                refine ⟨2342890968960227534216245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12495418501121213515819973 2342890968960227534216245)
                ·
                  refine ⟨219646028340021331332773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342890968960227534216245 219646028340021331332773)
                  ·
                    rfl

theorem cell22_1924916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1924916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924916 prefixEnd_1924916 := by exact prefixLift 1924916
  have htrace : WordTrace (prefixWord ++ tailWord_1924916) baseStart_1924916 baseEnd_1924916 := by
    simpa [prefixWord, tailWord_1924916, baseEnd_1924916] using wordTrace_append hprefix tailTrace_1924916
  have hstable : (prefixWord ++ tailWord_1924916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924916).length < 2 ^ (prefixWord ++ tailWord_1924916).sum := by decide
  have hdescent : baseEnd_1924916 < baseStart_1924916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924920 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_1924920 : Nat := 118140960795 + 1924920 * 2 ^ 59
def prefixEnd_1924920 : Nat := 4983230072969 + 3 ^ 40 * 1924920 * 2
def baseEnd_1924920 : Nat := 658939454301809316898307

theorem tailTrace_1924920 : CollatzResearch.WordTrace tailWord_1924920 prefixEnd_1924920 658939454301809316898307 := by
  unfold tailWord_1924920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103800093175532503986107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46805066790900710005314809 35103800093175532503986107)
  ·
    refine ⟨52655700139763298755979161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35103800093175532503986107 52655700139763298755979161)
    ·
      refine ⟨39491775104822474066984371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52655700139763298755979161 39491775104822474066984371)
      ·
        refine ⟨59237662657233711100476557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39491775104822474066984371 59237662657233711100476557)
        ·
          refine ⟨22214123496462641662678709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59237662657233711100476557 22214123496462641662678709)
          ·
            refine ⟨2082574077793372655876129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22214123496462641662678709 2082574077793372655876129)
            ·
              refine ⟨1561930558345029491907097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082574077793372655876129 1561930558345029491907097)
              ·
                refine ⟨1171447918758772118930323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561930558345029491907097 1171447918758772118930323)
                ·
                  refine ⟨1757171878138158178395485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171447918758772118930323 1757171878138158178395485)
                  ·
                    refine ⟨658939454301809316898307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757171878138158178395485 658939454301809316898307)
                    ·
                      rfl

theorem cell22_1924920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_1924920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924920 prefixEnd_1924920 := by exact prefixLift 1924920
  have htrace : WordTrace (prefixWord ++ tailWord_1924920) baseStart_1924920 baseEnd_1924920 := by
    simpa [prefixWord, tailWord_1924920, baseEnd_1924920] using wordTrace_append hprefix tailTrace_1924920
  have hstable : (prefixWord ++ tailWord_1924920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924920).length < 2 ^ (prefixWord ++ tailWord_1924920).sum := by decide
  have hdescent : baseEnd_1924920 < baseStart_1924920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924959 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_1924959 : Nat := 118140960795 + 1924959 * 2 ^ 59
def prefixEnd_1924959 : Nat := 4983230072969 + 3 ^ 40 * 1924959 * 2
def baseEnd_1924959 : Nat := 658952804798826215173187

theorem tailTrace_1924959 : CollatzResearch.WordTrace tailWord_1924959 prefixEnd_1924959 658952804798826215173187 := by
  unfold tailWord_1924959
  simp only [CollatzResearch.WordTrace]
  refine ⟨70209022633209774668641931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46806015088806516445761287 70209022633209774668641931)
  ·
    refine ⟨105313533949814662002962897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70209022633209774668641931 105313533949814662002962897)
    ·
      refine ⟨78985150462360996502222173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105313533949814662002962897 78985150462360996502222173)
      ·
        refine ⟨29619431423385373688333315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78985150462360996502222173 29619431423385373688333315)
        ·
          refine ⟨44429147135078060532499973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619431423385373688333315 44429147135078060532499973)
          ·
            refine ⟨8330465087827136349843745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44429147135078060532499973 8330465087827136349843745)
            ·
              refine ⟨6247848815870352262382809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330465087827136349843745 6247848815870352262382809)
              ·
                refine ⟨4685886611902764196787107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247848815870352262382809 4685886611902764196787107)
                ·
                  refine ⟨7028829917854146295180661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685886611902764196787107 7028829917854146295180661)
                  ·
                    refine ⟨658952804798826215173187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7028829917854146295180661 658952804798826215173187)
                    ·
                      rfl

theorem cell22_1924959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_1924959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924959 prefixEnd_1924959 := by exact prefixLift 1924959
  have htrace : WordTrace (prefixWord ++ tailWord_1924959) baseStart_1924959 baseEnd_1924959 := by
    simpa [prefixWord, tailWord_1924959, baseEnd_1924959] using wordTrace_append hprefix tailTrace_1924959
  have hstable : (prefixWord ++ tailWord_1924959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924959).length < 2 ^ (prefixWord ++ tailWord_1924959).sum := by decide
  have hdescent : baseEnd_1924959 < baseStart_1924959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924961 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 4]
def baseStart_1924961 : Nat := 118140960795 + 1924961 * 2 ^ 59
def prefixEnd_1924961 : Nat := 4983230072969 + 3 ^ 40 * 1924961 * 2
def baseEnd_1924961 : Nat := 219651163146566292207727

theorem tailTrace_1924961 : CollatzResearch.WordTrace tailWord_1924961 prefixEnd_1924961 219651163146566292207727 := by
  unfold tailWord_1924961
  simp only [CollatzResearch.WordTrace]
  refine ⟨70209095579202529010214737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46806063719468352673476491 70209095579202529010214737)
  ·
    refine ⟨52656821684401896757661053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70209095579202529010214737 52656821684401896757661053)
    ·
      refine ⟨19746308131650711284122895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52656821684401896757661053 19746308131650711284122895)
      ·
        refine ⟨29619462197476066926184343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746308131650711284122895 29619462197476066926184343)
        ·
          refine ⟨44429193296214100389276515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619462197476066926184343 44429193296214100389276515)
          ·
            refine ⟨66643789944321150583914773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44429193296214100389276515 66643789944321150583914773)
            ·
              refine ⟨3123927653640053933621005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66643789944321150583914773 3123927653640053933621005)
              ·
                refine ⟨1171472870115020225107877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123927653640053933621005 1171472870115020225107877)
                ·
                  refine ⟨219651163146566292207727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171472870115020225107877 219651163146566292207727)
                  ·
                    rfl

theorem cell22_1924961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_1924961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1924961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1924961 prefixEnd_1924961 := by exact prefixLift 1924961
  have htrace : WordTrace (prefixWord ++ tailWord_1924961) baseStart_1924961 baseEnd_1924961 := by
    simpa [prefixWord, tailWord_1924961, baseEnd_1924961] using wordTrace_append hprefix tailTrace_1924961
  have hstable : (prefixWord ++ tailWord_1924961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924961).length < 2 ^ (prefixWord ++ tailWord_1924961).sum := by decide
  have hdescent : baseEnd_1924961 < baseStart_1924961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925044 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1925044 : Nat := 118140960795 + 1925044 * 2 ^ 59
def prefixEnd_1925044 : Nat := 4983230072969 + 3 ^ 40 * 1925044 * 2
def baseEnd_1925044 : Nat := 658981902035914326797927

theorem tailTrace_1925044 : CollatzResearch.WordTrace tailWord_1925044 prefixEnd_1925044 658981902035914326797927 := by
  unfold tailWord_1925044
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106061418950917092743093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46808081891934556123657457 35106061418950917092743093)
  ·
    refine ⟨3291193258026648477444665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35106061418950917092743093 3291193258026648477444665)
    ·
      refine ⟨2468394943519986358083499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3291193258026648477444665 2468394943519986358083499)
      ·
        refine ⟨3702592415279979537125249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468394943519986358083499 3702592415279979537125249)
        ·
          refine ⟨2776944311459984652843937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702592415279979537125249 2776944311459984652843937)
          ·
            refine ⟨2082708233594988489632953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776944311459984652843937 2082708233594988489632953)
            ·
              refine ⟨1562031175196241367224715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082708233594988489632953 1562031175196241367224715)
              ·
                refine ⟨2343046762794362050837073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562031175196241367224715 2343046762794362050837073)
                ·
                  refine ⟨1757285072095771538127805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343046762794362050837073 1757285072095771538127805)
                  ·
                    refine ⟨658981902035914326797927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757285072095771538127805 658981902035914326797927)
                    ·
                      rfl

theorem cell22_1925044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1925044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925044 prefixEnd_1925044 := by exact prefixLift 1925044
  have htrace : WordTrace (prefixWord ++ tailWord_1925044) baseStart_1925044 baseEnd_1925044 := by
    simpa [prefixWord, tailWord_1925044, baseEnd_1925044] using wordTrace_append hprefix tailTrace_1925044
  have hstable : (prefixWord ++ tailWord_1925044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925044).length < 2 ^ (prefixWord ++ tailWord_1925044).sum := by decide
  have hdescent : baseEnd_1925044 < baseStart_1925044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925049 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_1925049 : Nat := 118140960795 + 1925049 * 2 ^ 59
def prefixEnd_1925049 : Nat := 4983230072969 + 3 ^ 40 * 1925049 * 2
def baseEnd_1925049 : Nat := 658983613638095980422911

theorem tailTrace_1925049 : CollatzResearch.WordTrace tailWord_1925049 prefixEnd_1925049 658983613638095980422911 := by
  unfold tailWord_1925049
  simp only [CollatzResearch.WordTrace]
  refine ⟨70212305202883720039418201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46808203468589146692945467 70212305202883720039418201)
  ·
    refine ⟨52659228902162790029563651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70212305202883720039418201 52659228902162790029563651)
    ·
      refine ⟨78988843353244185044345477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52659228902162790029563651 78988843353244185044345477)
      ·
        refine ⟨14810408128733284695814777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78988843353244185044345477 14810408128733284695814777)
        ·
          refine ⟨11107806096549963521861083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14810408128733284695814777 11107806096549963521861083)
          ·
            refine ⟨16661709144824945282791625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107806096549963521861083 16661709144824945282791625)
            ·
              refine ⟨12496281858618708962093719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16661709144824945282791625 12496281858618708962093719)
              ·
                refine ⟨18744422787928063443140579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496281858618708962093719 18744422787928063443140579)
                ·
                  refine ⟨28116634181892095164710869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18744422787928063443140579 28116634181892095164710869)
                  ·
                    refine ⟨658983613638095980422911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28116634181892095164710869 658983613638095980422911)
                    ·
                      rfl

theorem cell22_1925049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_1925049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925049 prefixEnd_1925049 := by exact prefixLift 1925049
  have htrace : WordTrace (prefixWord ++ tailWord_1925049) baseStart_1925049 baseEnd_1925049 := by
    simpa [prefixWord, tailWord_1925049, baseEnd_1925049] using wordTrace_append hprefix tailTrace_1925049
  have hstable : (prefixWord ++ tailWord_1925049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925049).length < 2 ^ (prefixWord ++ tailWord_1925049).sum := by decide
  have hdescent : baseEnd_1925049 < baseStart_1925049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925130 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_1925130 : Nat := 118140960795 + 1925130 * 2 ^ 59
def prefixEnd_1925130 : Nat := 4983230072969 + 3 ^ 40 * 1925130 * 2
def baseEnd_1925130 : Nat := 219670447197812923049221

theorem tailTrace_1925130 : CollatzResearch.WordTrace tailWord_1925130 prefixEnd_1925130 219670447197812923049221 := by
  unfold tailWord_1925130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17553814878897567718279211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46810173010393513915411229 17553814878897567718279211)
  ·
    refine ⟨26330722318346351577418817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17553814878897567718279211 26330722318346351577418817)
    ·
      refine ⟨19748041738759763683064113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26330722318346351577418817 19748041738759763683064113)
      ·
        refine ⟨14811031304069822762298085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19748041738759763683064113 14811031304069822762298085)
        ·
          refine ⟨2777068369513091767930891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14811031304069822762298085 2777068369513091767930891)
          ·
            refine ⟨4165602554269637651896337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777068369513091767930891 4165602554269637651896337)
            ·
              refine ⟨3124201915702228238922253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4165602554269637651896337 3124201915702228238922253)
              ·
                refine ⟨1171575718388335589595845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124201915702228238922253 1171575718388335589595845)
                ·
                  refine ⟨219670447197812923049221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171575718388335589595845 219670447197812923049221)
                  ·
                    rfl

theorem cell22_1925130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_1925130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925130 prefixEnd_1925130 := by exact prefixLift 1925130
  have htrace : WordTrace (prefixWord ++ tailWord_1925130) baseStart_1925130 baseEnd_1925130 := by
    simpa [prefixWord, tailWord_1925130, baseEnd_1925130] using wordTrace_append hprefix tailTrace_1925130
  have hstable : (prefixWord ++ tailWord_1925130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925130).length < 2 ^ (prefixWord ++ tailWord_1925130).sum := by decide
  have hdescent : baseEnd_1925130 < baseStart_1925130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925141 : List Nat := [1, 3, 2, 1, 5, 1, 9]
def baseStart_1925141 : Nat := 118140960795 + 1925141 * 2 ^ 59
def prefixEnd_1925141 : Nat := 4983230072969 + 3 ^ 40 * 1925141 * 2
def baseEnd_1925141 : Nat := 24407966930305126189727

theorem tailTrace_1925141 : CollatzResearch.WordTrace tailWord_1925141 prefixEnd_1925141 24407966930305126189727 := by
  unfold tailWord_1925141
  simp only [CollatzResearch.WordTrace]
  refine ⟨70215660718550419751767277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46810440479033613167844851 70215660718550419751767277)
  ·
    refine ⟨26330872769456407406912729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70215660718550419751767277 26330872769456407406912729)
    ·
      refine ⟨19748154577092305555184547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26330872769456407406912729 19748154577092305555184547)
      ·
        refine ⟨29622231865638458332776821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19748154577092305555184547 29622231865638458332776821)
        ·
          refine ⟨2777084237403605468697827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29622231865638458332776821 2777084237403605468697827)
          ·
            refine ⟨4165626356105408203046741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777084237403605468697827 4165626356105408203046741)
            ·
              refine ⟨24407966930305126189727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4165626356105408203046741 24407966930305126189727)
              ·
                rfl

theorem cell22_1925141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 9].length) (baseStart_1925141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925141 prefixEnd_1925141 := by exact prefixLift 1925141
  have htrace : WordTrace (prefixWord ++ tailWord_1925141) baseStart_1925141 baseEnd_1925141 := by
    simpa [prefixWord, tailWord_1925141, baseEnd_1925141] using wordTrace_append hprefix tailTrace_1925141
  have hstable : (prefixWord ++ tailWord_1925141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925141).length < 2 ^ (prefixWord ++ tailWord_1925141).sum := by decide
  have hdescent : baseEnd_1925141 < baseStart_1925141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925162 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1925162 : Nat := 118140960795 + 1925162 * 2 ^ 59
def prefixEnd_1925162 : Nat := 4983230072969 + 3 ^ 40 * 1925162 * 2
def baseEnd_1925162 : Nat := 659022295847401352347565

theorem tailTrace_1925162 : CollatzResearch.WordTrace tailWord_1925162 prefixEnd_1925162 659022295847401352347565 := by
  unfold tailWord_1925162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554106662868585084570435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46810951100982893558854493 17554106662868585084570435)
  ·
    refine ⟨26331159994302877626855653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554106662868585084570435 26331159994302877626855653)
    ·
      refine ⟨4937092498931789555035435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26331159994302877626855653 4937092498931789555035435)
      ·
        refine ⟨7405638748397684332553153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937092498931789555035435 7405638748397684332553153)
        ·
          refine ⟨5554229061298263249414865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405638748397684332553153 5554229061298263249414865)
          ·
            refine ⟨4165671795973697437061149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5554229061298263249414865 4165671795973697437061149)
            ·
              refine ⟨1562126923490136538897931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4165671795973697437061149 1562126923490136538897931)
              ·
                refine ⟨2343190385235204808346897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562126923490136538897931 2343190385235204808346897)
                ·
                  refine ⟨1757392788926403606260173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343190385235204808346897 1757392788926403606260173)
                  ·
                    refine ⟨659022295847401352347565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757392788926403606260173 659022295847401352347565)
                    ·
                      rfl

theorem cell22_1925162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1925162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925162 prefixEnd_1925162 := by exact prefixLift 1925162
  have htrace : WordTrace (prefixWord ++ tailWord_1925162) baseStart_1925162 baseEnd_1925162 := by
    simpa [prefixWord, tailWord_1925162, baseEnd_1925162] using wordTrace_append hprefix tailTrace_1925162
  have hstable : (prefixWord ++ tailWord_1925162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925162).length < 2 ^ (prefixWord ++ tailWord_1925162).sum := by decide
  have hdescent : baseEnd_1925162 < baseStart_1925162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925173 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1925173 : Nat := 118140960795 + 1925173 * 2 ^ 59
def prefixEnd_1925173 : Nat := 4983230072969 + 3 ^ 40 * 1925173 * 2
def baseEnd_1925173 : Nat := 659026061372200990322531

theorem tailTrace_1925173 : CollatzResearch.WordTrace tailWord_1925173 prefixEnd_1925173 659026061372200990322531 := by
  unfold tailWord_1925173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70216827854434489216932173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46811218569622992811288115 70216827854434489216932173)
  ·
    refine ⟨26331310445412933456349565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70216827854434489216932173 26331310445412933456349565)
    ·
      refine ⟨9874241417029850046131087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26331310445412933456349565 9874241417029850046131087)
      ·
        refine ⟨14811362125544775069196631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874241417029850046131087 14811362125544775069196631)
        ·
          refine ⟨22217043188317162603794947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14811362125544775069196631 22217043188317162603794947)
          ·
            refine ⟨33325564782475743905692421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22217043188317162603794947 33325564782475743905692421)
            ·
              refine ⟨6248543396714201982317329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33325564782475743905692421 6248543396714201982317329)
              ·
                refine ⟨4686407547535651486737997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248543396714201982317329 4686407547535651486737997)
                ·
                  refine ⟨1757402830325869307526749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4686407547535651486737997 1757402830325869307526749)
                  ·
                    refine ⟨659026061372200990322531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757402830325869307526749 659026061372200990322531)
                    ·
                      rfl

theorem cell22_1925173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1925173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925173 prefixEnd_1925173 := by exact prefixLift 1925173
  have htrace : WordTrace (prefixWord ++ tailWord_1925173) baseStart_1925173 baseEnd_1925173 := by
    simpa [prefixWord, tailWord_1925173, baseEnd_1925173] using wordTrace_append hprefix tailTrace_1925173
  have hstable : (prefixWord ++ tailWord_1925173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925173).length < 2 ^ (prefixWord ++ tailWord_1925173).sum := by decide
  have hdescent : baseEnd_1925173 < baseStart_1925173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925248 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_1925248 : Nat := 118140960795 + 1925248 * 2 ^ 59
def prefixEnd_1925248 : Nat := 4983230072969 + 3 ^ 40 * 1925248 * 2
def baseEnd_1925248 : Nat := 219683911801641931565767

theorem tailTrace_1925248 : CollatzResearch.WordTrace tailWord_1925248 prefixEnd_1925248 219683911801641931565767 := by
  unfold tailWord_1925248
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109781664581388512956199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46813042219441851350608265 35109781664581388512956199)
  ·
    refine ⟨52664672496872082769434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35109781664581388512956199 52664672496872082769434299)
    ·
      refine ⟨78997008745308124154151449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52664672496872082769434299 78997008745308124154151449)
      ·
        refine ⟨59247756558981093115613587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78997008745308124154151449 59247756558981093115613587)
        ·
          refine ⟨88871634838471639673420381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59247756558981093115613587 88871634838471639673420381)
          ·
            refine ⟨33326863064426864877532643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88871634838471639673420381 33326863064426864877532643)
            ·
              refine ⟨49990294596640297316298965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33326863064426864877532643 49990294596640297316298965)
              ·
                refine ⟨1171647529608756968350757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49990294596640297316298965 1171647529608756968350757)
                ·
                  refine ⟨219683911801641931565767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171647529608756968350757 219683911801641931565767)
                  ·
                    rfl

theorem cell22_1925248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_1925248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925248 prefixEnd_1925248 := by exact prefixLift 1925248
  have htrace : WordTrace (prefixWord ++ tailWord_1925248) baseStart_1925248 baseEnd_1925248 := by
    simpa [prefixWord, tailWord_1925248, baseEnd_1925248] using wordTrace_append hprefix tailTrace_1925248
  have hstable : (prefixWord ++ tailWord_1925248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925248).length < 2 ^ (prefixWord ++ tailWord_1925248).sum := by decide
  have hdescent : baseEnd_1925248 < baseStart_1925248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925280 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_1925280 : Nat := 118140960795 + 1925280 * 2 ^ 59
def prefixEnd_1925280 : Nat := 4983230072969 + 3 ^ 40 * 1925280 * 2
def baseEnd_1925280 : Nat := 659062689658888377897203

theorem tailTrace_1925280 : CollatzResearch.WordTrace tailWord_1925280 prefixEnd_1925280 659062689658888377897203 := by
  unfold tailWord_1925280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35110365232523423245538647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46813820310031230994051529 35110365232523423245538647)
  ·
    refine ⟨52665547848785134868307971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35110365232523423245538647 52665547848785134868307971)
    ·
      refine ⟨78998321773177702302461957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52665547848785134868307971 78998321773177702302461957)
      ·
        refine ⟨14812185332470819181711617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78998321773177702302461957 14812185332470819181711617)
        ·
          refine ⟨11109138999353114386283713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14812185332470819181711617 11109138999353114386283713)
          ·
            refine ⟨8331854249514835789712785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11109138999353114386283713 8331854249514835789712785)
            ·
              refine ⟨6248890687136126842284589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8331854249514835789712785 6248890687136126842284589)
              ·
                refine ⟨2343334007676047565856721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6248890687136126842284589 2343334007676047565856721)
                ·
                  refine ⟨1757500505757035674392541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343334007676047565856721 1757500505757035674392541)
                  ·
                    refine ⟨659062689658888377897203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757500505757035674392541 659062689658888377897203)
                    ·
                      rfl

theorem cell22_1925280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_1925280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925280 prefixEnd_1925280 := by exact prefixLift 1925280
  have htrace : WordTrace (prefixWord ++ tailWord_1925280) baseStart_1925280 baseEnd_1925280 := by
    simpa [prefixWord, tailWord_1925280, baseEnd_1925280] using wordTrace_append hprefix tailTrace_1925280
  have hstable : (prefixWord ++ tailWord_1925280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925280).length < 2 ^ (prefixWord ++ tailWord_1925280).sum := by decide
  have hdescent : baseEnd_1925280 < baseStart_1925280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925301 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1925301 : Nat := 118140960795 + 1925301 * 2 ^ 59
def prefixEnd_1925301 : Nat := 4983230072969 + 3 ^ 40 * 1925301 * 2
def baseEnd_1925301 : Nat := 659069878388051323122139

theorem tailTrace_1925301 : CollatzResearch.WordTrace tailWord_1925301 prefixEnd_1925301 659069878388051323122139 := by
  unfold tailWord_1925301
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221496397970767077591757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46814330931980511385061171 70221496397970767077591757)
  ·
    refine ⟨26333061149239037654096909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70221496397970767077591757 26333061149239037654096909)
    ·
      refine ⟨9874897930964639120286341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26333061149239037654096909 9874897930964639120286341)
      ·
        refine ⟨1851543362055869835053689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9874897930964639120286341 1851543362055869835053689)
        ·
          refine ⟨1388657521541902376290267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851543362055869835053689 1388657521541902376290267)
          ·
            refine ⟨2082986282312853564435401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388657521541902376290267 2082986282312853564435401)
            ·
              refine ⟨1562239711734640173326551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082986282312853564435401 1562239711734640173326551)
              ·
                refine ⟨2343359567601960259989827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562239711734640173326551 2343359567601960259989827)
                ·
                  refine ⟨3515039351402940389984741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343359567601960259989827 3515039351402940389984741)
                  ·
                    refine ⟨659069878388051323122139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515039351402940389984741 659069878388051323122139)
                    ·
                      rfl

theorem cell22_1925301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1925301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925301 prefixEnd_1925301 := by exact prefixLift 1925301
  have htrace : WordTrace (prefixWord ++ tailWord_1925301) baseStart_1925301 baseEnd_1925301 := by
    simpa [prefixWord, tailWord_1925301, baseEnd_1925301] using wordTrace_append hprefix tailTrace_1925301
  have hstable : (prefixWord ++ tailWord_1925301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925301).length < 2 ^ (prefixWord ++ tailWord_1925301).sum := by decide
  have hdescent : baseEnd_1925301 < baseStart_1925301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925314 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1925314 : Nat := 118140960795 + 1925314 * 2 ^ 59
def prefixEnd_1925314 : Nat := 4983230072969 + 3 ^ 40 * 1925314 * 2
def baseEnd_1925314 : Nat := 659074328553723622547099

theorem tailTrace_1925314 : CollatzResearch.WordTrace tailWord_1925314 prefixEnd_1925314 659074328553723622547099 := by
  unfold tailWord_1925314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555492636730917574453749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46814647031282446865209997 17555492636730917574453749)
  ·
    refine ⟨1645827434693523522605039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17555492636730917574453749 1645827434693523522605039)
    ·
      refine ⟨2468741152040285283907559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645827434693523522605039 2468741152040285283907559)
      ·
        refine ⟨3703111728060427925861339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468741152040285283907559 3703111728060427925861339)
        ·
          refine ⟨5554667592090641888792009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703111728060427925861339 5554667592090641888792009)
          ·
            refine ⟨4166000694067981416594007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5554667592090641888792009 4166000694067981416594007)
            ·
              refine ⟨6249001041101972124891011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166000694067981416594007 6249001041101972124891011)
              ·
                refine ⟨9373501561652958187336517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249001041101972124891011 9373501561652958187336517)
                ·
                  refine ⟨1757531542809929660125597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9373501561652958187336517 1757531542809929660125597)
                  ·
                    refine ⟨659074328553723622547099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757531542809929660125597 659074328553723622547099)
                    ·
                      rfl

theorem cell22_1925314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1925314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925314 prefixEnd_1925314 := by exact prefixLift 1925314
  have htrace : WordTrace (prefixWord ++ tailWord_1925314) baseStart_1925314 baseEnd_1925314 := by
    simpa [prefixWord, tailWord_1925314, baseEnd_1925314] using wordTrace_append hprefix tailTrace_1925314
  have hstable : (prefixWord ++ tailWord_1925314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925314).length < 2 ^ (prefixWord ++ tailWord_1925314).sum := by decide
  have hdescent : baseEnd_1925314 < baseStart_1925314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925338 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1925338 : Nat := 118140960795 + 1925338 * 2 ^ 59
def prefixEnd_1925338 : Nat := 4983230072969 + 3 ^ 40 * 1925338 * 2
def baseEnd_1925338 : Nat := 219694181414731853315675

theorem tailTrace_1925338 : CollatzResearch.WordTrace tailWord_1925338 prefixEnd_1925338 219694181414731853315675 := by
  unfold tailWord_1925338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555711474709180599172167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46815230599224481597792445 17555711474709180599172167)
  ·
    refine ⟨26333567212063770898758251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17555711474709180599172167 26333567212063770898758251)
    ·
      refine ⟨39500350818095656348137377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26333567212063770898758251 39500350818095656348137377)
      ·
        refine ⟨29625263113571742261103033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39500350818095656348137377 29625263113571742261103033)
        ·
          refine ⟨22218947335178806695827275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29625263113571742261103033 22218947335178806695827275)
          ·
            refine ⟨33328421002768210043740913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22218947335178806695827275 33328421002768210043740913)
            ·
              refine ⟨24996315752076157532805685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33328421002768210043740913 24996315752076157532805685)
              ·
                refine ⟨2343404601757139768700533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24996315752076157532805685 2343404601757139768700533)
                ·
                  refine ⟨219694181414731853315675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343404601757139768700533 219694181414731853315675)
                  ·
                    rfl

theorem cell22_1925338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1925338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925338 prefixEnd_1925338 := by exact prefixLift 1925338
  have htrace : WordTrace (prefixWord ++ tailWord_1925338) baseStart_1925338 baseEnd_1925338 := by
    simpa [prefixWord, tailWord_1925338, baseEnd_1925338] using wordTrace_append hprefix tailTrace_1925338
  have hstable : (prefixWord ++ tailWord_1925338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925338).length < 2 ^ (prefixWord ++ tailWord_1925338).sum := by decide
  have hdescent : baseEnd_1925338 < baseStart_1925338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925359 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 1, 3]
def baseStart_1925359 : Nat := 118140960795 + 1925359 * 2 ^ 59
def prefixEnd_1925359 : Nat := 4983230072969 + 3 ^ 40 * 1925359 * 2
def baseEnd_1925359 : Nat := 659089732973358505171961

theorem tailTrace_1925359 : CollatzResearch.WordTrace tailWord_1925359 prefixEnd_1925359 659089732973358505171961 := by
  unfold tailWord_1925359
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223611831760642983203131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46815741221173761988802087 70223611831760642983203131)
  ·
    refine ⟨105335417747640964474804697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70223611831760642983203131 105335417747640964474804697)
    ·
      refine ⟨79001563310730723356103523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105335417747640964474804697 79001563310730723356103523)
      ·
        refine ⟨118502344966096085034155285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79001563310730723356103523 118502344966096085034155285)
        ·
          refine ⟨5554797420285753985976029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118502344966096085034155285 5554797420285753985976029)
          ·
            refine ⟨2083049032607157744741011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5554797420285753985976029 2083049032607157744741011)
            ·
              refine ⟨3124573548910736617111517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083049032607157744741011 3124573548910736617111517)
              ·
                refine ⟨1171715080841526231416819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124573548910736617111517 1171715080841526231416819)
                ·
                  refine ⟨1757572621262289347125229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171715080841526231416819 1757572621262289347125229)
                  ·
                    refine ⟨659089732973358505171961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757572621262289347125229 659089732973358505171961)
                    ·
                      rfl

theorem cell22_1925359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_1925359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925359 prefixEnd_1925359 := by exact prefixLift 1925359
  have htrace : WordTrace (prefixWord ++ tailWord_1925359) baseStart_1925359 baseEnd_1925359 := by
    simpa [prefixWord, tailWord_1925359, baseEnd_1925359] using wordTrace_append hprefix tailTrace_1925359
  have hstable : (prefixWord ++ tailWord_1925359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925359).length < 2 ^ (prefixWord ++ tailWord_1925359).sum := by decide
  have hdescent : baseEnd_1925359 < baseStart_1925359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925434 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_1925434 : Nat := 118140960795 + 1925434 * 2 ^ 59
def prefixEnd_1925434 : Nat := 4983230072969 + 3 ^ 40 * 1925434 * 2
def baseEnd_1925434 : Nat := 219705135668694436515577

theorem tailTrace_1925434 : CollatzResearch.WordTrace tailWord_1925434 prefixEnd_1925434 219705135668694436515577 := by
  unfold tailWord_1925434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17556586826622232698045839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46817564870992620528122237 17556586826622232698045839)
  ·
    refine ⟨26334880239933349047068759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17556586826622232698045839 26334880239933349047068759)
    ·
      refine ⟨39502320359900023570603139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26334880239933349047068759 39502320359900023570603139)
      ·
        refine ⟨59253480539850035355904709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39502320359900023570603139 59253480539850035355904709)
        ·
          refine ⟨11110027601221881629232133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59253480539850035355904709 11110027601221881629232133)
          ·
            refine ⟨2083130175229102805481025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11110027601221881629232133 2083130175229102805481025)
            ·
              refine ⟨1562347631421827104110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083130175229102805481025 1562347631421827104110769)
              ·
                refine ⟨1171760723566370328083077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562347631421827104110769 1171760723566370328083077)
                ·
                  refine ⟨219705135668694436515577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171760723566370328083077 219705135668694436515577)
                  ·
                    rfl

theorem cell22_1925434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_1925434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925434 prefixEnd_1925434 := by exact prefixLift 1925434
  have htrace : WordTrace (prefixWord ++ tailWord_1925434) baseStart_1925434 baseEnd_1925434 := by
    simpa [prefixWord, tailWord_1925434, baseEnd_1925434] using wordTrace_append hprefix tailTrace_1925434
  have hstable : (prefixWord ++ tailWord_1925434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925434).length < 2 ^ (prefixWord ++ tailWord_1925434).sum := by decide
  have hdescent : baseEnd_1925434 < baseStart_1925434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925490 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1925490 : Nat := 118140960795 + 1925490 * 2 ^ 59
def prefixEnd_1925490 : Nat := 4983230072969 + 3 ^ 40 * 1925490 * 2
def baseEnd_1925490 : Nat := 219711525650172610048853

theorem tailTrace_1925490 : CollatzResearch.WordTrace tailWord_1925490 prefixEnd_1925490 219711525650172610048853 := by
  unfold tailWord_1925490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17557097448571513089055481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46818926529524034904147949 17557097448571513089055481)
  ·
    refine ⟨13167823086428634816791611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17557097448571513089055481 13167823086428634816791611)
    ·
      refine ⟨19751734629642952225187417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13167823086428634816791611 19751734629642952225187417)
      ·
        refine ⟨14813800972232214168890563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19751734629642952225187417 14813800972232214168890563)
        ·
          refine ⟨22220701458348321253335845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813800972232214168890563 22220701458348321253335845)
          ·
            refine ⟨4166381523440310235000471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22220701458348321253335845 4166381523440310235000471)
            ·
              refine ⟨6249572285160465352500707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166381523440310235000471 6249572285160465352500707)
              ·
                refine ⟨9374358427740698028751061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249572285160465352500707 9374358427740698028751061)
                ·
                  refine ⟨219711525650172610048853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9374358427740698028751061 219711525650172610048853)
                  ·
                    rfl

theorem cell22_1925490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1925490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925490 prefixEnd_1925490 := by exact prefixLift 1925490
  have htrace : WordTrace (prefixWord ++ tailWord_1925490) baseStart_1925490 baseEnd_1925490 := by
    simpa [prefixWord, tailWord_1925490, baseEnd_1925490] using wordTrace_append hprefix tailTrace_1925490
  have hstable : (prefixWord ++ tailWord_1925490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925490).length < 2 ^ (prefixWord ++ tailWord_1925490).sum := by decide
  have hdescent : baseEnd_1925490 < baseStart_1925490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925603 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 4]
def baseStart_1925603 : Nat := 118140960795 + 1925603 * 2 ^ 59
def prefixEnd_1925603 : Nat := 4983230072969 + 3 ^ 40 * 1925603 * 2
def baseEnd_1925603 : Nat := 219724419719941067357071

theorem tailTrace_1925603 : CollatzResearch.WordTrace tailWord_1925603 prefixEnd_1925603 219724419719941067357071 := by
  unfold tailWord_1925603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70232511242876672655085463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46821674161917781770056975 70232511242876672655085463)
  ·
    refine ⟨105348766864315008982628195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70232511242876672655085463 105348766864315008982628195)
    ·
      refine ⟨158023150296472513473942293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105348766864315008982628195 158023150296472513473942293)
      ·
        refine ⟨7407335170147149069091045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158023150296472513473942293 7407335170147149069091045)
        ·
          refine ⟨1388875344402590450454571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7407335170147149069091045 1388875344402590450454571)
          ·
            refine ⟨2083313016603885675681857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388875344402590450454571 2083313016603885675681857)
            ·
              refine ⟨1562484762452914256761393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083313016603885675681857 1562484762452914256761393)
              ·
                refine ⟨1171863571839685692571045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562484762452914256761393 1171863571839685692571045)
                ·
                  refine ⟨219724419719941067357071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171863571839685692571045 219724419719941067357071)
                  ·
                    rfl

theorem cell22_1925603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 4].length) (baseStart_1925603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925603 prefixEnd_1925603 := by exact prefixLift 1925603
  have htrace : WordTrace (prefixWord ++ tailWord_1925603) baseStart_1925603 baseEnd_1925603 := by
    simpa [prefixWord, tailWord_1925603, baseEnd_1925603] using wordTrace_append hprefix tailTrace_1925603
  have hstable : (prefixWord ++ tailWord_1925603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925603).length < 2 ^ (prefixWord ++ tailWord_1925603).sum := by decide
  have hdescent : baseEnd_1925603 < baseStart_1925603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925612 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_1925612 : Nat := 118140960795 + 1925612 * 2 ^ 59
def prefixEnd_1925612 : Nat := 4983230072969 + 3 ^ 40 * 1925612 * 2
def baseEnd_1925612 : Nat := 659176340043750178596185

theorem tailTrace_1925612 : CollatzResearch.WordTrace tailWord_1925612 prefixEnd_1925612 659176340043750178596185 := by
  unfold tailWord_1925612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116419749922033596081545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46821892999896044794775393 35116419749922033596081545)
  ·
    refine ⟨26337314812441525197061159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35116419749922033596081545 26337314812441525197061159)
    ·
      refine ⟨39505972218662287795591739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26337314812441525197061159 39505972218662287795591739)
      ·
        refine ⟨59258958327993431693387609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39505972218662287795591739 59258958327993431693387609)
        ·
          refine ⟨44444218745995073770040707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59258958327993431693387609 44444218745995073770040707)
          ·
            refine ⟨66666328118992610655061061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44444218745995073770040707 66666328118992610655061061)
            ·
              refine ⟨12499936522311114497823949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66666328118992610655061061 12499936522311114497823949)
              ·
                refine ⟨4687476195866667936683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12499936522311114497823949 4687476195866667936683981)
                ·
                  refine ⟨1757803573450000476256493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4687476195866667936683981 1757803573450000476256493)
                  ·
                    refine ⟨659176340043750178596185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757803573450000476256493 659176340043750178596185)
                    ·
                      rfl

theorem cell22_1925612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_1925612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925612 prefixEnd_1925612 := by exact prefixLift 1925612
  have htrace : WordTrace (prefixWord ++ tailWord_1925612) baseStart_1925612 baseEnd_1925612 := by
    simpa [prefixWord, tailWord_1925612, baseEnd_1925612] using wordTrace_append hprefix tailTrace_1925612
  have hstable : (prefixWord ++ tailWord_1925612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925612).length < 2 ^ (prefixWord ++ tailWord_1925612).sum := by decide
  have hdescent : baseEnd_1925612 < baseStart_1925612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925640 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1925640 : Nat := 118140960795 + 1925640 * 2 ^ 59
def prefixEnd_1925640 : Nat := 4983230072969 + 3 ^ 40 * 1925640 * 2
def baseEnd_1925640 : Nat := 659185925015967438896099

theorem tailTrace_1925640 : CollatzResearch.WordTrace tailWord_1925640 prefixEnd_1925640 659185925015967438896099 := by
  unfold tailWord_1925640
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116930371871313987091187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46822573829161751982788249 35116930371871313987091187)
  ·
    refine ⟨52675395557806970980636781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35116930371871313987091187 52675395557806970980636781)
    ·
      refine ⟨19753273334177614117738793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52675395557806970980636781 19753273334177614117738793)
      ·
        refine ⟨14814955000633210588304095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19753273334177614117738793 14814955000633210588304095)
        ·
          refine ⟨22222432500949815882456143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14814955000633210588304095 22222432500949815882456143)
          ·
            refine ⟨33333648751424723823684215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22222432500949815882456143 33333648751424723823684215)
            ·
              refine ⟨50000473127137085735526323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33333648751424723823684215 50000473127137085735526323)
              ·
                refine ⟨75000709690705628603289485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50000473127137085735526323 75000709690705628603289485)
                ·
                  refine ⟨28125266134014610726233557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75000709690705628603289485 28125266134014610726233557)
                  ·
                    refine ⟨659185925015967438896099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28125266134014610726233557 659185925015967438896099)
                    ·
                      rfl

theorem cell22_1925640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1925640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925640 prefixEnd_1925640 := by exact prefixLift 1925640
  have htrace : WordTrace (prefixWord ++ tailWord_1925640) baseStart_1925640 baseEnd_1925640 := by
    simpa [prefixWord, tailWord_1925640, baseEnd_1925640] using wordTrace_append hprefix tailTrace_1925640
  have hstable : (prefixWord ++ tailWord_1925640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925640).length < 2 ^ (prefixWord ++ tailWord_1925640).sum := by decide
  have hdescent : baseEnd_1925640 < baseStart_1925640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925646 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_1925646 : Nat := 118140960795 + 1925646 * 2 ^ 59
def prefixEnd_1925646 : Nat := 4983230072969 + 3 ^ 40 * 1925646 * 2
def baseEnd_1925646 : Nat := 659187978938585423246081

theorem tailTrace_1925646 : CollatzResearch.WordTrace tailWord_1925646 prefixEnd_1925646 659187978938585423246081 := by
  unfold tailWord_1925646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779259947715111374862599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46822719721147260665933861 8779259947715111374862599)
  ·
    refine ⟨13168889921572667062293899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8779259947715111374862599 13168889921572667062293899)
    ·
      refine ⟨19753334882359000593440849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168889921572667062293899 19753334882359000593440849)
      ·
        refine ⟨14815001161769250445080637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19753334882359000593440849 14815001161769250445080637)
        ·
          refine ⟨5555625435663468916905239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14815001161769250445080637 5555625435663468916905239)
          ·
            refine ⟨8333438153495203375357859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555625435663468916905239 8333438153495203375357859)
            ·
              refine ⟨12500157230242805063036789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333438153495203375357859 12500157230242805063036789)
              ·
                refine ⟨1171889740335262974659699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12500157230242805063036789 1171889740335262974659699)
                ·
                  refine ⟨1757834610502894461989549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171889740335262974659699 1757834610502894461989549)
                  ·
                    refine ⟨659187978938585423246081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757834610502894461989549 659187978938585423246081)
                    ·
                      rfl

theorem cell22_1925646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_1925646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925646 prefixEnd_1925646 := by exact prefixLift 1925646
  have htrace : WordTrace (prefixWord ++ tailWord_1925646) baseStart_1925646 baseEnd_1925646 := by
    simpa [prefixWord, tailWord_1925646, baseEnd_1925646] using wordTrace_append hprefix tailTrace_1925646
  have hstable : (prefixWord ++ tailWord_1925646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925646).length < 2 ^ (prefixWord ++ tailWord_1925646).sum := by decide
  have hdescent : baseEnd_1925646 < baseStart_1925646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925689 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1925689 : Nat := 118140960795 + 1925689 * 2 ^ 59
def prefixEnd_1925689 : Nat := 4983230072969 + 3 ^ 40 * 1925689 * 2
def baseEnd_1925689 : Nat := 659202698717347644420949

theorem tailTrace_1925689 : CollatzResearch.WordTrace tailWord_1925689 prefixEnd_1925689 659202698717347644420949 := by
  unfold tailWord_1925689
  simp only [CollatzResearch.WordTrace]
  refine ⟨70235647920565109342716121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46823765280376739561810747 70235647920565109342716121)
  ·
    refine ⟨52676735940423832007037091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70235647920565109342716121 52676735940423832007037091)
    ·
      refine ⟨79015103910635748010555637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52676735940423832007037091 79015103910635748010555637)
      ·
        refine ⟨7407665991622101375989591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79015103910635748010555637 7407665991622101375989591)
        ·
          refine ⟨11111498987433152063984387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407665991622101375989591 11111498987433152063984387)
          ·
            refine ⟨16667248481149728095976581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111498987433152063984387 16667248481149728095976581)
            ·
              refine ⟨3125109090215574017995609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16667248481149728095976581 3125109090215574017995609)
              ·
                refine ⟨2343831817661680513496707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125109090215574017995609 2343831817661680513496707)
                ·
                  refine ⟨3515747726492520770245061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343831817661680513496707 3515747726492520770245061)
                  ·
                    refine ⟨659202698717347644420949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515747726492520770245061 659202698717347644420949)
                    ·
                      rfl

theorem cell22_1925689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1925689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925689 prefixEnd_1925689 := by exact prefixLift 1925689
  have htrace : WordTrace (prefixWord ++ tailWord_1925689) baseStart_1925689 baseEnd_1925689 := by
    simpa [prefixWord, tailWord_1925689, baseEnd_1925689] using wordTrace_append hprefix tailTrace_1925689
  have hstable : (prefixWord ++ tailWord_1925689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925689).length < 2 ^ (prefixWord ++ tailWord_1925689).sum := by decide
  have hdescent : baseEnd_1925689 < baseStart_1925689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925717 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1925717 : Nat := 118140960795 + 1925717 * 2 ^ 59
def prefixEnd_1925717 : Nat := 4983230072969 + 3 ^ 40 * 1925717 * 2
def baseEnd_1925717 : Nat := 659212283689564904720863

theorem tailTrace_1925717 : CollatzResearch.WordTrace tailWord_1925717 prefixEnd_1925717 659212283689564904720863 := by
  unfold tailWord_1925717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70236669164463670124735405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46824446109642446749823603 70236669164463670124735405)
  ·
    refine ⟨26338750936673876296775777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70236669164463670124735405 26338750936673876296775777)
    ·
      refine ⟨19754063202505407222581833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26338750936673876296775777 19754063202505407222581833)
      ·
        refine ⟨14815547401879055416936375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19754063202505407222581833 14815547401879055416936375)
        ·
          refine ⟨22223321102818583125404563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815547401879055416936375 22223321102818583125404563)
          ·
            refine ⟨33334981654227874688106845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22223321102818583125404563 33334981654227874688106845)
            ·
              refine ⟨12500618120335453008040067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33334981654227874688106845 12500618120335453008040067)
              ·
                refine ⟨18750927180503179512060101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12500618120335453008040067 18750927180503179512060101)
                ·
                  refine ⟨3515798846344346158511269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18750927180503179512060101 3515798846344346158511269)
                  ·
                    refine ⟨659212283689564904720863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515798846344346158511269 659212283689564904720863)
                    ·
                      rfl

theorem cell22_1925717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1925717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925717 prefixEnd_1925717 := by exact prefixLift 1925717
  have htrace : WordTrace (prefixWord ++ tailWord_1925717) baseStart_1925717 baseEnd_1925717 := by
    simpa [prefixWord, tailWord_1925717, baseEnd_1925717] using wordTrace_append hprefix tailTrace_1925717
  have hstable : (prefixWord ++ tailWord_1925717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925717).length < 2 ^ (prefixWord ++ tailWord_1925717).sum := by decide
  have hdescent : baseEnd_1925717 < baseStart_1925717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925719 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 2, 3]
def baseStart_1925719 : Nat := 118140960795 + 1925719 * 2 ^ 59
def prefixEnd_1925719 : Nat := 4983230072969 + 3 ^ 40 * 1925719 * 2
def baseEnd_1925719 : Nat := 659212968330437566170857

theorem tailTrace_1925719 : CollatzResearch.WordTrace tailWord_1925719 prefixEnd_1925719 659212968330437566170857 := by
  unfold tailWord_1925719
  simp only [CollatzResearch.WordTrace]
  refine ⟨70236742110456424466308211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46824494740304282977538807 70236742110456424466308211)
  ·
    refine ⟨105355113165684636699462317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70236742110456424466308211 105355113165684636699462317)
    ·
      refine ⟨39508167437131738762298369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105355113165684636699462317 39508167437131738762298369)
      ·
        refine ⟨29631125577848804071723777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39508167437131738762298369 29631125577848804071723777)
        ·
          refine ⟨22223344183386603053792833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29631125577848804071723777 22223344183386603053792833)
          ·
            refine ⟨16667508137539952290344625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22223344183386603053792833 16667508137539952290344625)
            ·
              refine ⟨12500631103154964217758469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16667508137539952290344625 12500631103154964217758469)
              ·
                refine ⟨2343868331841555790829713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12500631103154964217758469 2343868331841555790829713)
                ·
                  refine ⟨1757901248881166843122285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343868331841555790829713 1757901248881166843122285)
                  ·
                    refine ⟨659212968330437566170857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1757901248881166843122285 659212968330437566170857)
                    ·
                      rfl

theorem cell22_1925719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_1925719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925719 prefixEnd_1925719 := by exact prefixLift 1925719
  have htrace : WordTrace (prefixWord ++ tailWord_1925719) baseStart_1925719 baseEnd_1925719 := by
    simpa [prefixWord, tailWord_1925719, baseEnd_1925719] using wordTrace_append hprefix tailTrace_1925719
  have hstable : (prefixWord ++ tailWord_1925719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925719).length < 2 ^ (prefixWord ++ tailWord_1925719).sum := by decide
  have hdescent : baseEnd_1925719 < baseStart_1925719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925732 : List Nat := [2, 3, 1, 1, 2, 2, 4, 7]
def baseStart_1925732 : Nat := 118140960795 + 1925732 * 2 ^ 59
def prefixEnd_1925732 : Nat := 4983230072969 + 3 ^ 40 * 1925732 * 2
def baseEnd_1925732 : Nat := 73246379832901096177313

theorem tailTrace_1925732 : CollatzResearch.WordTrace tailWord_1925732 prefixEnd_1925732 73246379832901096177313 := by
  unfold tailWord_1925732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118608129704663843265725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46824810839606218457687633 35118608129704663843265725)
  ·
    refine ⟨13169478048639248941224647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35118608129704663843265725 13169478048639248941224647)
    ·
      refine ⟨19754217072958873411836971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169478048639248941224647 19754217072958873411836971)
      ·
        refine ⟨29631325609438310117755457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754217072958873411836971 29631325609438310117755457)
        ·
          refine ⟨22223494207078732588316593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29631325609438310117755457 22223494207078732588316593)
          ·
            refine ⟨16667620655309049441237445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22223494207078732588316593 16667620655309049441237445)
            ·
              refine ⟨3125178872870446770232021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16667620655309049441237445 3125178872870446770232021)
              ·
                refine ⟨73246379832901096177313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3125178872870446770232021 73246379832901096177313)
                ·
                  rfl

theorem cell22_1925732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_1925732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925732 prefixEnd_1925732 := by exact prefixLift 1925732
  have htrace : WordTrace (prefixWord ++ tailWord_1925732) baseStart_1925732 baseEnd_1925732 := by
    simpa [prefixWord, tailWord_1925732, baseEnd_1925732] using wordTrace_append hprefix tailTrace_1925732
  have hstable : (prefixWord ++ tailWord_1925732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925732).length < 2 ^ (prefixWord ++ tailWord_1925732).sum := by decide
  have hdescent : baseEnd_1925732 < baseStart_1925732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925869 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1925869 : Nat := 118140960795 + 1925869 * 2 ^ 59
def prefixEnd_1925869 : Nat := 4983230072969 + 3 ^ 40 * 1925869 * 2
def baseEnd_1925869 : Nat := 659264316395887174920397

theorem tailTrace_1925869 : CollatzResearch.WordTrace tailWord_1925869 prefixEnd_1925869 659264316395887174920397 := by
  unfold tailWord_1925869
  simp only [CollatzResearch.WordTrace]
  refine ⟨70242213059913000084268661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46828142039942000056179107 70242213059913000084268661)
  ·
    refine ⟨6585207474366843757900187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70242213059913000084268661 6585207474366843757900187)
    ·
      refine ⟨9877811211550265636850281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585207474366843757900187 9877811211550265636850281)
      ·
        refine ⟨7408358408662699227637711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9877811211550265636850281 7408358408662699227637711)
        ·
          refine ⟨11112537612994048841456567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408358408662699227637711 11112537612994048841456567)
          ·
            refine ⟨16668806419491073262184851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112537612994048841456567 16668806419491073262184851)
            ·
              refine ⟨25003209629236609893277277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16668806419491073262184851 25003209629236609893277277)
              ·
                refine ⟨9376203610963728709978979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25003209629236609893277277 9376203610963728709978979)
                ·
                  refine ⟨14064305416445593064968469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9376203610963728709978979 14064305416445593064968469)
                  ·
                    refine ⟨659264316395887174920397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14064305416445593064968469 659264316395887174920397)
                    ·
                      rfl

theorem cell22_1925869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1925869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925869 prefixEnd_1925869 := by exact prefixLift 1925869
  have htrace : WordTrace (prefixWord ++ tailWord_1925869) baseStart_1925869 baseEnd_1925869 := by
    simpa [prefixWord, tailWord_1925869, baseEnd_1925869] using wordTrace_append hprefix tailTrace_1925869
  have hstable : (prefixWord ++ tailWord_1925869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925869).length < 2 ^ (prefixWord ++ tailWord_1925869).sum := by decide
  have hdescent : baseEnd_1925869 < baseStart_1925869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925884 : List Nat := [2, 2, 2, 1, 3, 4, 8]
def baseStart_1925884 : Nat := 118140960795 + 1925884 * 2 ^ 59
def prefixEnd_1925884 : Nat := 4983230072969 + 3 ^ 40 * 1925884 * 2
def baseEnd_1925884 : Nat := 24417387081571560585013

theorem tailTrace_1925884 : CollatzResearch.WordTrace tailWord_1925884 prefixEnd_1925884 24417387081571560585013 := by
  unfold tailWord_1925884
  simp only [CollatzResearch.WordTrace]
  refine ⟨35121380077429328823032353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46828506769905771764043137 35121380077429328823032353)
  ·
    refine ⟨26341035058071996617274265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35121380077429328823032353 26341035058071996617274265)
    ·
      refine ⟨19755776293553997462955699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26341035058071996617274265 19755776293553997462955699)
      ·
        refine ⟨29633664440330996194433549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19755776293553997462955699 29633664440330996194433549)
        ·
          refine ⟨11112624165124123572912581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29633664440330996194433549 11112624165124123572912581)
          ·
            refine ⟨2083617030960773169921109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11112624165124123572912581 2083617030960773169921109)
            ·
              refine ⟨24417387081571560585013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2083617030960773169921109 24417387081571560585013)
              ·
                rfl

theorem cell22_1925884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 8].length) (baseStart_1925884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925884 prefixEnd_1925884 := by exact prefixLift 1925884
  have htrace : WordTrace (prefixWord ++ tailWord_1925884) baseStart_1925884 baseEnd_1925884 := by
    simpa [prefixWord, tailWord_1925884, baseEnd_1925884] using wordTrace_append hprefix tailTrace_1925884
  have hstable : (prefixWord ++ tailWord_1925884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925884).length < 2 ^ (prefixWord ++ tailWord_1925884).sum := by decide
  have hdescent : baseEnd_1925884 < baseStart_1925884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925886 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1925886 : Nat := 118140960795 + 1925886 * 2 ^ 59
def prefixEnd_1925886 : Nat := 4983230072969 + 3 ^ 40 * 1925886 * 2
def baseEnd_1925886 : Nat := 659270135843304797245345

theorem tailTrace_1925886 : CollatzResearch.WordTrace tailWord_1925886 prefixEnd_1925886 659270135843304797245345 := by
  unfold tailWord_1925886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780354137606426498454689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46828555400567607991758341 8780354137606426498454689)
  ·
    refine ⟨6585265603204819873841017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8780354137606426498454689 6585265603204819873841017)
    ·
      refine ⟨4938949202403614905380763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585265603204819873841017 4938949202403614905380763)
      ·
        refine ⟨7408423803605422358071145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938949202403614905380763 7408423803605422358071145)
        ·
          refine ⟨5556317852704066768553359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408423803605422358071145 5556317852704066768553359)
          ·
            refine ⟨8334476779056100152830039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556317852704066768553359 8334476779056100152830039)
            ·
              refine ⟨12501715168584150229245059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334476779056100152830039 12501715168584150229245059)
              ·
                refine ⟨18752572752876225343867589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501715168584150229245059 18752572752876225343867589)
                ·
                  refine ⟨3516107391164292251975173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18752572752876225343867589 3516107391164292251975173)
                  ·
                    refine ⟨659270135843304797245345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516107391164292251975173 659270135843304797245345)
                    ·
                      rfl

theorem cell22_1925886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1925886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925886 prefixEnd_1925886 := by exact prefixLift 1925886
  have htrace : WordTrace (prefixWord ++ tailWord_1925886) baseStart_1925886 baseEnd_1925886 := by
    simpa [prefixWord, tailWord_1925886, baseEnd_1925886] using wordTrace_append hprefix tailTrace_1925886
  have hstable : (prefixWord ++ tailWord_1925886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925886).length < 2 ^ (prefixWord ++ tailWord_1925886).sum := by decide
  have hdescent : baseEnd_1925886 < baseStart_1925886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925890 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1925890 : Nat := 118140960795 + 1925890 * 2 ^ 59
def prefixEnd_1925890 : Nat := 4983230072969 + 3 ^ 40 * 1925890 * 2
def baseEnd_1925890 : Nat := 219757168375016706715111

theorem tailTrace_1925890 : CollatzResearch.WordTrace tailWord_1925890 prefixEnd_1925890 219757168375016706715111 := by
  unfold tailWord_1925890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560744748209230167695781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46828652661891280447188749 17560744748209230167695781)
  ·
    refine ⟨3292639640289230656442959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17560744748209230167695781 3292639640289230656442959)
    ·
      refine ⟨4938959460433845984664439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292639640289230656442959 4938959460433845984664439)
      ·
        refine ⟨7408439190650768976996659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938959460433845984664439 7408439190650768976996659)
        ·
          refine ⟨11112658785976153465494989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408439190650768976996659 11112658785976153465494989)
          ·
            refine ⟨4167247044741057549560621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11112658785976153465494989 4167247044741057549560621)
            ·
              refine ⟨1562717641777896581085233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4167247044741057549560621 1562717641777896581085233)
              ·
                refine ⟨1172038231333422435813925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562717641777896581085233 1172038231333422435813925)
                ·
                  refine ⟨219757168375016706715111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1172038231333422435813925 219757168375016706715111)
                  ·
                    rfl

theorem cell22_1925890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1925890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925890 prefixEnd_1925890 := by exact prefixLift 1925890
  have htrace : WordTrace (prefixWord ++ tailWord_1925890) baseStart_1925890 baseEnd_1925890 := by
    simpa [prefixWord, tailWord_1925890, baseEnd_1925890] using wordTrace_append hprefix tailTrace_1925890
  have hstable : (prefixWord ++ tailWord_1925890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925890).length < 2 ^ (prefixWord ++ tailWord_1925890).sum := by decide
  have hdescent : baseEnd_1925890 < baseStart_1925890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925944 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_1925944 : Nat := 118140960795 + 1925944 * 2 ^ 59
def prefixEnd_1925944 : Nat := 4983230072969 + 3 ^ 40 * 1925944 * 2
def baseEnd_1925944 : Nat := 659289990428611979295167

theorem tailTrace_1925944 : CollatzResearch.WordTrace tailWord_1925944 prefixEnd_1925944 659289990428611979295167 := by
  unfold tailWord_1925944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35122474267320643946624443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46829965689760858595499257 35122474267320643946624443)
  ·
    refine ⟨52683711400980965919936665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35122474267320643946624443 52683711400980965919936665)
    ·
      refine ⟨39512783550735724439952499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52683711400980965919936665 39512783550735724439952499)
      ·
        refine ⟨59269175326103586659928749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39512783550735724439952499 59269175326103586659928749)
        ·
          refine ⟨22225940747288844997473281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59269175326103586659928749 22225940747288844997473281)
          ·
            refine ⟨16669455560466633748104961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22225940747288844997473281 16669455560466633748104961)
            ·
              refine ⟨12502091670349975311078721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16669455560466633748104961 12502091670349975311078721)
              ·
                refine ⟨9376568752762481483309041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502091670349975311078721 9376568752762481483309041)
                ·
                  refine ⟨7032426564571861112481781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9376568752762481483309041 7032426564571861112481781)
                  ·
                    refine ⟨659289990428611979295167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7032426564571861112481781 659289990428611979295167)
                    ·
                      rfl

theorem cell22_1925944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_1925944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1925944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1925944 prefixEnd_1925944 := by exact prefixLift 1925944
  have htrace : WordTrace (prefixWord ++ tailWord_1925944) baseStart_1925944 baseEnd_1925944 := by
    simpa [prefixWord, tailWord_1925944, baseEnd_1925944] using wordTrace_append hprefix tailTrace_1925944
  have hstable : (prefixWord ++ tailWord_1925944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925944).length < 2 ^ (prefixWord ++ tailWord_1925944).sum := by decide
  have hdescent : baseEnd_1925944 < baseStart_1925944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926019 : List Nat := [1, 1, 1, 3, 4, 1, 2, 9]
def baseStart_1926019 : Nat := 118140960795 + 1926019 * 2 ^ 59
def prefixEnd_1926019 : Nat := 4983230072969 + 3 ^ 40 * 1926019 * 2
def baseEnd_1926019 : Nat := 73257296051259642629993

theorem tailTrace_1926019 : CollatzResearch.WordTrace tailWord_1926019 prefixEnd_1926019 73257296051259642629993 := by
  unfold tailWord_1926019
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247684009369575702229111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46831789339579717134819407 70247684009369575702229111)
  ·
    refine ⟨105371526014054363553343667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70247684009369575702229111 105371526014054363553343667)
    ·
      refine ⟨158057289021081545330015501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105371526014054363553343667 158057289021081545330015501)
      ·
        refine ⟨59271483382905579498755813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158057289021081545330015501 59271483382905579498755813)
        ·
          refine ⟨11113403134294796156016715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59271483382905579498755813 11113403134294796156016715)
          ·
            refine ⟨16670104701442194234025073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113403134294796156016715 16670104701442194234025073)
            ·
              refine ⟨12502578526081645675518805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16670104701442194234025073 12502578526081645675518805)
              ·
                refine ⟨73257296051259642629993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12502578526081645675518805 73257296051259642629993)
                ·
                  rfl

theorem cell22_1926019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_1926019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926019 prefixEnd_1926019 := by exact prefixLift 1926019
  have htrace : WordTrace (prefixWord ++ tailWord_1926019) baseStart_1926019 baseEnd_1926019 := by
    simpa [prefixWord, tailWord_1926019, baseEnd_1926019] using wordTrace_append hprefix tailTrace_1926019
  have hstable : (prefixWord ++ tailWord_1926019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926019).length < 2 ^ (prefixWord ++ tailWord_1926019).sum := by decide
  have hdescent : baseEnd_1926019 < baseStart_1926019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926023 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1926023 : Nat := 118140960795 + 1926023 * 2 ^ 59
def prefixEnd_1926023 : Nat := 4983230072969 + 3 ^ 40 * 1926023 * 2
def baseEnd_1926023 : Nat := 659317033743082106569925

theorem tailTrace_1926023 : CollatzResearch.WordTrace tailWord_1926023 prefixEnd_1926023 659317033743082106569925 := by
  unfold tailWord_1926023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247829901355084385374723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46831886600903389590249815 70247829901355084385374723)
  ·
    refine ⟨105371744852032626578062085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70247829901355084385374723 105371744852032626578062085)
    ·
      refine ⟨19757202159756117483386641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105371744852032626578062085 19757202159756117483386641)
      ·
        refine ⟨14817901619817088112539981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19757202159756117483386641 14817901619817088112539981)
        ·
          refine ⟨5556713107431408042202493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14817901619817088112539981 5556713107431408042202493)
          ·
            refine ⟨2083767415286778015825935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5556713107431408042202493 2083767415286778015825935)
            ·
              refine ⟨3125651122930167023738903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083767415286778015825935 3125651122930167023738903)
              ·
                refine ⟨4688476684395250535608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125651122930167023738903 4688476684395250535608355)
                ·
                  refine ⟨7032715026592875803412533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688476684395250535608355 7032715026592875803412533)
                  ·
                    refine ⟨659317033743082106569925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7032715026592875803412533 659317033743082106569925)
                    ·
                      rfl

theorem cell22_1926023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1926023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926023 prefixEnd_1926023 := by exact prefixLift 1926023
  have htrace : WordTrace (prefixWord ++ tailWord_1926023) baseStart_1926023 baseEnd_1926023 := by
    simpa [prefixWord, tailWord_1926023, baseEnd_1926023] using wordTrace_append hprefix tailTrace_1926023
  have hstable : (prefixWord ++ tailWord_1926023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926023).length < 2 ^ (prefixWord ++ tailWord_1926023).sum := by decide
  have hdescent : baseEnd_1926023 < baseStart_1926023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926036 : List Nat := [2, 4, 2, 1, 1, 1, 3, 8]
def baseStart_1926036 : Nat := 118140960795 + 1926036 * 2 ^ 59
def prefixEnd_1926036 : Nat := 4983230072969 + 3 ^ 40 * 1926036 * 2
def baseEnd_1926036 : Nat := 73257942656528267332765

theorem tailTrace_1926036 : CollatzResearch.WordTrace tailWord_1926036 prefixEnd_1926036 73257942656528267332765 := by
  unfold tailWord_1926036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124152025153993802798981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46832202700205325070398641 35124152025153993802798981)
  ·
    refine ⟨6585778504716373838024809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35124152025153993802798981 6585778504716373838024809)
    ·
      refine ⟨4939333878537280378518607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585778504716373838024809 4939333878537280378518607)
      ·
        refine ⟨7409000817805920567777911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939333878537280378518607 7409000817805920567777911)
        ·
          refine ⟨11113501226708880851666867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409000817805920567777911 11113501226708880851666867)
          ·
            refine ⟨16670251840063321277500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113501226708880851666867 16670251840063321277500301)
            ·
              refine ⟨6251344440023745479062613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16670251840063321277500301 6251344440023745479062613)
              ·
                refine ⟨73257942656528267332765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6251344440023745479062613 73257942656528267332765)
                ·
                  rfl

theorem cell22_1926036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_1926036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926036 prefixEnd_1926036 := by exact prefixLift 1926036
  have htrace : WordTrace (prefixWord ++ tailWord_1926036) baseStart_1926036 baseEnd_1926036 := by
    simpa [prefixWord, tailWord_1926036, baseEnd_1926036] using wordTrace_append hprefix tailTrace_1926036
  have hstable : (prefixWord ++ tailWord_1926036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926036).length < 2 ^ (prefixWord ++ tailWord_1926036).sum := by decide
  have hdescent : baseEnd_1926036 < baseStart_1926036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926042 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1926042 : Nat := 118140960795 + 1926042 * 2 ^ 59
def prefixEnd_1926042 : Nat := 4983230072969 + 3 ^ 40 * 1926042 * 2
def baseEnd_1926042 : Nat := 219774512610457463448289

theorem tailTrace_1926042 : CollatzResearch.WordTrace tailWord_1926042 prefixEnd_1926042 219774512610457463448289 := by
  unfold tailWord_1926042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562130722071562657579095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46832348592190833753544253 17562130722071562657579095)
  ·
    refine ⟨26343196083107343986368643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562130722071562657579095 26343196083107343986368643)
    ·
      refine ⟨39514794124661015979552965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26343196083107343986368643 39514794124661015979552965)
      ·
        refine ⟨7409023898373940496166181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39514794124661015979552965 7409023898373940496166181)
        ·
          refine ⟨1389191980945113843031159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7409023898373940496166181 1389191980945113843031159)
          ·
            refine ⟨2083787971417670764546739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389191980945113843031159 2083787971417670764546739)
            ·
              refine ⟨3125681957126506146820109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083787971417670764546739 3125681957126506146820109)
              ·
                refine ⟨1172130733922439805057541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125681957126506146820109 1172130733922439805057541)
                ·
                  refine ⟨219774512610457463448289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1172130733922439805057541 219774512610457463448289)
                  ·
                    rfl

theorem cell22_1926042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1926042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926042 prefixEnd_1926042 := by exact prefixLift 1926042
  have htrace : WordTrace (prefixWord ++ tailWord_1926042) baseStart_1926042 baseEnd_1926042 := by
    simpa [prefixWord, tailWord_1926042, baseEnd_1926042] using wordTrace_append hprefix tailTrace_1926042
  have hstable : (prefixWord ++ tailWord_1926042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926042).length < 2 ^ (prefixWord ++ tailWord_1926042).sum := by decide
  have hdescent : baseEnd_1926042 < baseStart_1926042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926051 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 5, 3]
def baseStart_1926051 : Nat := 118140960795 + 1926051 * 2 ^ 59
def prefixEnd_1926051 : Nat := 4983230072969 + 3 ^ 40 * 1926051 * 2
def baseEnd_1926051 : Nat := 659326618715299366869839

theorem tailTrace_1926051 : CollatzResearch.WordTrace tailWord_1926051 prefixEnd_1926051 659326618715299366869839 := by
  unfold tailWord_1926051
  simp only [CollatzResearch.WordTrace]
  refine ⟨70248851145253645167394007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46832567430169096778262671 70248851145253645167394007)
  ·
    refine ⟨105373276717880467751091011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70248851145253645167394007 105373276717880467751091011)
    ·
      refine ⟨158059915076820701626636517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105373276717880467751091011 158059915076820701626636517)
      ·
        refine ⟨29636234076903881554994347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158059915076820701626636517 29636234076903881554994347)
        ·
          refine ⟨44454351115355822332491521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29636234076903881554994347 44454351115355822332491521)
          ·
            refine ⟨33340763336516866749368641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44454351115355822332491521 33340763336516866749368641)
            ·
              refine ⟨25005572502387650062026481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33340763336516866749368641 25005572502387650062026481)
              ·
                refine ⟨18754179376790737546519861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25005572502387650062026481 18754179376790737546519861)
                ·
                  refine ⟨1758204316574131644986237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18754179376790737546519861 1758204316574131644986237)
                  ·
                    refine ⟨659326618715299366869839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758204316574131644986237 659326618715299366869839)
                    ·
                      rfl

theorem cell22_1926051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].length) (baseStart_1926051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926051 prefixEnd_1926051 := by exact prefixLift 1926051
  have htrace : WordTrace (prefixWord ++ tailWord_1926051) baseStart_1926051 baseEnd_1926051 := by
    simpa [prefixWord, tailWord_1926051, baseEnd_1926051] using wordTrace_append hprefix tailTrace_1926051
  have hstable : (prefixWord ++ tailWord_1926051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926051).length < 2 ^ (prefixWord ++ tailWord_1926051).sum := by decide
  have hdescent : baseEnd_1926051 < baseStart_1926051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926119 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1926119 : Nat := 118140960795 + 1926119 * 2 ^ 59
def prefixEnd_1926119 : Nat := 4983230072969 + 3 ^ 40 * 1926119 * 2
def baseEnd_1926119 : Nat := 659349896504969856169631

theorem tailTrace_1926119 : CollatzResearch.WordTrace tailWord_1926119 prefixEnd_1926119 659349896504969856169631 := by
  unfold tailWord_1926119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70251331309007292780869411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46834220872671528520579607 70251331309007292780869411)
  ·
    refine ⟨105376996963510939171304117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70251331309007292780869411 105376996963510939171304117)
    ·
      refine ⟨9879093465329150547309761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105376996963510939171304117 9879093465329150547309761)
      ·
        refine ⟨7409320098996862910482321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9879093465329150547309761 7409320098996862910482321)
        ·
          refine ⟨5556990074247647182861741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409320098996862910482321 5556990074247647182861741)
          ·
            refine ⟨2083871277842867693573153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5556990074247647182861741 2083871277842867693573153)
            ·
              refine ⟨1562903458382150770179865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083871277842867693573153 1562903458382150770179865)
              ·
                refine ⟨1172177593786613077634899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562903458382150770179865 1172177593786613077634899)
                ·
                  refine ⟨1758266390679919616452349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172177593786613077634899 1758266390679919616452349)
                  ·
                    refine ⟨659349896504969856169631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758266390679919616452349 659349896504969856169631)
                    ·
                      rfl

theorem cell22_1926119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1926119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926119 prefixEnd_1926119 := by exact prefixLift 1926119
  have htrace : WordTrace (prefixWord ++ tailWord_1926119) baseStart_1926119 baseEnd_1926119 := by
    simpa [prefixWord, tailWord_1926119, baseEnd_1926119] using wordTrace_append hprefix tailTrace_1926119
  have hstable : (prefixWord ++ tailWord_1926119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926119).length < 2 ^ (prefixWord ++ tailWord_1926119).sum := by decide
  have hdescent : baseEnd_1926119 < baseStart_1926119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926130 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1926130 : Nat := 118140960795 + 1926130 * 2 ^ 59
def prefixEnd_1926130 : Nat := 4983230072969 + 3 ^ 40 * 1926130 * 2
def baseEnd_1926130 : Nat := 659353662029769494144597

theorem tailTrace_1926130 : CollatzResearch.WordTrace tailWord_1926130 prefixEnd_1926130 659353662029769494144597 := by
  unfold tailWord_1926130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562933127991860414879961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46834488341311627773013229 17562933127991860414879961)
  ·
    refine ⟨13172199845993895311159971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17562933127991860414879961 13172199845993895311159971)
    ·
      refine ⟨19758299768990842966739957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172199845993895311159971 19758299768990842966739957)
      ·
        refine ⟨1852340603342891528131871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19758299768990842966739957 1852340603342891528131871)
        ·
          refine ⟨2778510905014337292197807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852340603342891528131871 2778510905014337292197807)
          ·
            refine ⟨4167766357521505938296711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778510905014337292197807 4167766357521505938296711)
            ·
              refine ⟨6251649536282258907445067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167766357521505938296711 6251649536282258907445067)
              ·
                refine ⟨9377474304423388361167601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251649536282258907445067 9377474304423388361167601)
                ·
                  refine ⟨7033105728317541270875701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377474304423388361167601 7033105728317541270875701)
                  ·
                    refine ⟨659353662029769494144597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7033105728317541270875701 659353662029769494144597)
                    ·
                      rfl

theorem cell22_1926130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1926130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926130 prefixEnd_1926130 := by exact prefixLift 1926130
  have htrace : WordTrace (prefixWord ++ tailWord_1926130) baseStart_1926130 baseEnd_1926130 := by
    simpa [prefixWord, tailWord_1926130, baseEnd_1926130] using wordTrace_append hprefix tailTrace_1926130
  have hstable : (prefixWord ++ tailWord_1926130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926130).length < 2 ^ (prefixWord ++ tailWord_1926130).sum := by decide
  have hdescent : baseEnd_1926130 < baseStart_1926130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926158 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1926158 : Nat := 118140960795 + 1926158 * 2 ^ 59
def prefixEnd_1926158 : Nat := 4983230072969 + 3 ^ 40 * 1926158 * 2
def baseEnd_1926158 : Nat := 659363247001986754444511

theorem tailTrace_1926158 : CollatzResearch.WordTrace tailWord_1926158 prefixEnd_1926158 659363247001986754444511 := by
  unfold tailWord_1926158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781594219483250305192391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46835169170577334961026085 8781594219483250305192391)
  ·
    refine ⟨13172391329224875457788587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8781594219483250305192391 13172391329224875457788587)
    ·
      refine ⟨19758586993837313186682881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172391329224875457788587 19758586993837313186682881)
      ·
        refine ⟨14818940245377984890012161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19758586993837313186682881 14818940245377984890012161)
        ·
          refine ⟨11114205184033488667509121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14818940245377984890012161 11114205184033488667509121)
          ·
            refine ⟨8335653888025116500631841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114205184033488667509121 8335653888025116500631841)
            ·
              refine ⟨6251740416018837375473881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335653888025116500631841 6251740416018837375473881)
              ·
                refine ⟨4688805312014128031605411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251740416018837375473881 4688805312014128031605411)
                ·
                  refine ⟨7033207968021192047408117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688805312014128031605411 7033207968021192047408117)
                  ·
                    refine ⟨659363247001986754444511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7033207968021192047408117 659363247001986754444511)
                    ·
                      rfl

theorem cell22_1926158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1926158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926158 prefixEnd_1926158 := by exact prefixLift 1926158
  have htrace : WordTrace (prefixWord ++ tailWord_1926158) baseStart_1926158 baseEnd_1926158 := by
    simpa [prefixWord, tailWord_1926158, baseEnd_1926158] using wordTrace_append hprefix tailTrace_1926158
  have hstable : (prefixWord ++ tailWord_1926158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926158).length < 2 ^ (prefixWord ++ tailWord_1926158).sum := by decide
  have hdescent : baseEnd_1926158 < baseStart_1926158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926175 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 2, 3]
def baseStart_1926175 : Nat := 118140960795 + 1926175 * 2 ^ 59
def prefixEnd_1926175 : Nat := 4983230072969 + 3 ^ 40 * 1926175 * 2
def baseEnd_1926175 : Nat := 659369066449404376769459

theorem tailTrace_1926175 : CollatzResearch.WordTrace tailWord_1926175 prefixEnd_1926175 659369066449404376769459 := by
  unfold tailWord_1926175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70253373796804414344907979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46835582531202942896605319 70253373796804414344907979)
  ·
    refine ⟨105380060695206621517361969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70253373796804414344907979 105380060695206621517361969)
    ·
      refine ⟨79035045521404966138021477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105380060695206621517361969 79035045521404966138021477)
      ·
        refine ⟨14819071035263431150879027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79035045521404966138021477 14819071035263431150879027)
        ·
          refine ⟨22228606552895146726318541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819071035263431150879027 22228606552895146726318541)
          ·
            refine ⟨8335727457335680022369453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22228606552895146726318541 8335727457335680022369453)
            ·
              refine ⟨3125897796500880008388545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8335727457335680022369453 3125897796500880008388545)
              ·
                refine ⟨2344423347375660006291409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125897796500880008388545 2344423347375660006291409)
                ·
                  refine ⟨1758317510531745004718557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344423347375660006291409 1758317510531745004718557)
                  ·
                    refine ⟨659369066449404376769459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1758317510531745004718557 659369066449404376769459)
                    ·
                      rfl

theorem cell22_1926175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_1926175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926175 prefixEnd_1926175 := by exact prefixLift 1926175
  have htrace : WordTrace (prefixWord ++ tailWord_1926175) baseStart_1926175 baseEnd_1926175 := by
    simpa [prefixWord, tailWord_1926175, baseEnd_1926175] using wordTrace_append hprefix tailTrace_1926175
  have hstable : (prefixWord ++ tailWord_1926175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926175).length < 2 ^ (prefixWord ++ tailWord_1926175).sum := by decide
  have hdescent : baseEnd_1926175 < baseStart_1926175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926205 : List Nat := [1, 4, 1, 3, 1, 4, 2, 6]
def baseStart_1926205 : Nat := 118140960795 + 1926205 * 2 ^ 59
def prefixEnd_1926205 : Nat := 4983230072969 + 3 ^ 40 * 1926205 * 2
def baseEnd_1926205 : Nat := 73264370673610477613263

theorem tailTrace_1926205 : CollatzResearch.WordTrace tailWord_1926205 prefixEnd_1926205 73264370673610477613263 := by
  unfold tailWord_1926205
  simp only [CollatzResearch.WordTrace]
  refine ⟨70254467986695729468500069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46836311991130486312333379 70254467986695729468500069)
  ·
    refine ⟨13172712747505449275343763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70254467986695729468500069 13172712747505449275343763)
    ·
      refine ⟨19759069121258173913015645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172712747505449275343763 19759069121258173913015645)
      ·
        refine ⟨7409650920471815217380867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19759069121258173913015645 7409650920471815217380867)
        ·
          refine ⟨11114476380707722826071301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409650920471815217380867 11114476380707722826071301)
          ·
            refine ⟨2083964321382698029888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11114476380707722826071301 2083964321382698029888369)
            ·
              refine ⟨1562973241037023522416277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083964321382698029888369 1562973241037023522416277)
              ·
                refine ⟨73264370673610477613263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1562973241037023522416277 73264370673610477613263)
                ·
                  rfl

theorem cell22_1926205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 6].length) (baseStart_1926205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926205 prefixEnd_1926205 := by exact prefixLift 1926205
  have htrace : WordTrace (prefixWord ++ tailWord_1926205) baseStart_1926205 baseEnd_1926205 := by
    simpa [prefixWord, tailWord_1926205, baseEnd_1926205] using wordTrace_append hprefix tailTrace_1926205
  have hstable : (prefixWord ++ tailWord_1926205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926205).length < 2 ^ (prefixWord ++ tailWord_1926205).sum := by decide
  have hdescent : baseEnd_1926205 < baseStart_1926205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926216 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_1926216 : Nat := 118140960795 + 1926216 * 2 ^ 59
def prefixEnd_1926216 : Nat := 4983230072969 + 3 ^ 40 * 1926216 * 2
def baseEnd_1926216 : Nat := 219794367195764645498111

theorem tailTrace_1926216 : CollatzResearch.WordTrace tailWord_1926216 prefixEnd_1926216 219794367195764645498111 := by
  unfold tailWord_1926216
  simp only [CollatzResearch.WordTrace]
  refine ⟨35127434594827939173575251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46836579459770585564767001 35127434594827939173575251)
  ·
    refine ⟨52691151892241908760362877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35127434594827939173575251 52691151892241908760362877)
    ·
      refine ⟨19759181959590715785136079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52691151892241908760362877 19759181959590715785136079)
      ·
        refine ⟨29638772939386073677704119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759181959590715785136079 29638772939386073677704119)
        ·
          refine ⟨44458159409079110516556179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29638772939386073677704119 44458159409079110516556179)
          ·
            refine ⟨66687239113618665774834269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44458159409079110516556179 66687239113618665774834269)
            ·
              refine ⟨25007714667606999665562851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66687239113618665774834269 25007714667606999665562851)
              ·
                refine ⟨37511572001410499498344277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25007714667606999665562851 37511572001410499498344277)
                ·
                  refine ⟨219794367195764645498111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37511572001410499498344277 219794367195764645498111)
                  ·
                    rfl

theorem cell22_1926216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_1926216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926216 prefixEnd_1926216 := by exact prefixLift 1926216
  have htrace : WordTrace (prefixWord ++ tailWord_1926216) baseStart_1926216 baseEnd_1926216 := by
    simpa [prefixWord, tailWord_1926216, baseEnd_1926216] using wordTrace_append hprefix tailTrace_1926216
  have hstable : (prefixWord ++ tailWord_1926216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926216).length < 2 ^ (prefixWord ++ tailWord_1926216).sum := by decide
  have hdescent : baseEnd_1926216 < baseStart_1926216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926250 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1926250 : Nat := 118140960795 + 1926250 * 2 ^ 59
def prefixEnd_1926250 : Nat := 4983230072969 + 3 ^ 40 * 1926250 * 2
def baseEnd_1926250 : Nat := 219798246827376393714743

theorem tailTrace_1926250 : CollatzResearch.WordTrace tailWord_1926250 prefixEnd_1926250 219798246827376393714743 := by
  unfold tailWord_1926250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564027317883175538472051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46837406181021801435925469 17564027317883175538472051)
  ·
    refine ⟨26346040976824763307708077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564027317883175538472051 26346040976824763307708077)
    ·
      refine ⟨9879765366309286240390529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26346040976824763307708077 9879765366309286240390529)
      ·
        refine ⟨7409824024731964680292897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9879765366309286240390529 7409824024731964680292897)
        ·
          refine ⟨5557368018548973510219673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409824024731964680292897 5557368018548973510219673)
          ·
            refine ⟨4168026013911730132664755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557368018548973510219673 4168026013911730132664755)
            ·
              refine ⟨6252039020867595198997133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168026013911730132664755 6252039020867595198997133)
              ·
                refine ⟨2344514632825348199623925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252039020867595198997133 2344514632825348199623925)
                ·
                  refine ⟨219798246827376393714743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2344514632825348199623925 219798246827376393714743)
                  ·
                    rfl

theorem cell22_1926250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1926250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1926250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1926250 prefixEnd_1926250 := by exact prefixLift 1926250
  have htrace : WordTrace (prefixWord ++ tailWord_1926250) baseStart_1926250 baseEnd_1926250 := by
    simpa [prefixWord, tailWord_1926250, baseEnd_1926250] using wordTrace_append hprefix tailTrace_1926250
  have hstable : (prefixWord ++ tailWord_1926250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926250).length < 2 ^ (prefixWord ++ tailWord_1926250).sum := by decide
  have hdescent : baseEnd_1926250 < baseStart_1926250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
