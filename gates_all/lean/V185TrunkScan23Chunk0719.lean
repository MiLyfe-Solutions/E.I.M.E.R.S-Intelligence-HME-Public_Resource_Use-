import V185TrunkScan23Chunk0718

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4251187 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 1, 4]
def baseStart_4251187 : Nat := 118140960795 + 4251187 * 2 ^ 59
def prefixEnd_4251187 : Nat := 4983230072969 + 3 ^ 40 * 4251187 * 2
def baseEnd_4251187 : Nat := 727634094381787981670551

theorem tailTrace_4251187 : CollatzResearch.WordTrace tailWord_4251187 prefixEnd_4251187 727634094381787981670551 := by
  unfold tailWord_4251187
  simp only [CollatzResearch.WordTrace]
  refine ⟨155053528049683018781319815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103369018699788679187546543 155053528049683018781319815)
  ·
    refine ⟨232580292074524528171979723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155053528049683018781319815 232580292074524528171979723)
    ·
      refine ⟨348870438111786792257969585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232580292074524528171979723 348870438111786792257969585)
      ·
        refine ⟨261652828583840094193477189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348870438111786792257969585 261652828583840094193477189)
        ·
          refine ⟨49059905359470017661276973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261652828583840094193477189 49059905359470017661276973)
          ·
            refine ⟨18397464509801256622978865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49059905359470017661276973 18397464509801256622978865)
            ·
              refine ⟨13798098382350942467234149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18397464509801256622978865 13798098382350942467234149)
              ·
                refine ⟨2587143446690801712606403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13798098382350942467234149 2587143446690801712606403)
                ·
                  refine ⟨3880715170036202568909605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587143446690801712606403 3880715170036202568909605)
                  ·
                    refine ⟨727634094381787981670551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880715170036202568909605 727634094381787981670551)
                    ·
                      rfl

theorem cell23_4251187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 4].length) (baseStart_4251187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251187 prefixEnd_4251187 := by exact prefixLift 4251187
  have htrace : WordTrace (prefixWord ++ tailWord_4251187) baseStart_4251187 baseEnd_4251187 := by
    simpa [prefixWord, tailWord_4251187, baseEnd_4251187] using wordTrace_append hprefix tailTrace_4251187
  have hstable : (prefixWord ++ tailWord_4251187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251187).length < 2 ^ (prefixWord ++ tailWord_4251187).sum := by decide
  have hdescent : baseEnd_4251187 < baseStart_4251187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251237 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_4251237 : Nat := 118140960795 + 4251237 * 2 ^ 59
def prefixEnd_4251237 : Nat := 4983230072969 + 3 ^ 40 * 4251237 * 2
def baseEnd_4251237 : Nat := 2182927957178088749386423

theorem tailTrace_4251237 : CollatzResearch.WordTrace tailWord_4251237 prefixEnd_4251237 2182927957178088749386423 := by
  unfold tailWord_4251237
  simp only [CollatzResearch.WordTrace]
  refine ⟨155055351699501877320639965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103370234466334584880426643 155055351699501877320639965)
  ·
    refine ⟨58145756887313203995239987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155055351699501877320639965 58145756887313203995239987)
    ·
      refine ⟨87218635330969805992859981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58145756887313203995239987 87218635330969805992859981)
      ·
        refine ⟨32706988249113677247322493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87218635330969805992859981 32706988249113677247322493)
        ·
          refine ⟨12265120593417628967745935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32706988249113677247322493 12265120593417628967745935)
          ·
            refine ⟨18397680890126443451618903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12265120593417628967745935 18397680890126443451618903)
            ·
              refine ⟨27596521335189665177428355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18397680890126443451618903 27596521335189665177428355)
              ·
                refine ⟨41394782002784497766142533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27596521335189665177428355 41394782002784497766142533)
                ·
                  refine ⟨7761521625522093331151725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41394782002784497766142533 7761521625522093331151725)
                  ·
                    refine ⟨2910570609570784999181897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7761521625522093331151725 2910570609570784999181897)
                    ·
                      refine ⟨2182927957178088749386423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910570609570784999181897 2182927957178088749386423)
                      ·
                        rfl

theorem cell23_4251237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_4251237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251237 prefixEnd_4251237 := by exact prefixLift 4251237
  have htrace : WordTrace (prefixWord ++ tailWord_4251237) baseStart_4251237 baseEnd_4251237 := by
    simpa [prefixWord, tailWord_4251237, baseEnd_4251237] using wordTrace_append hprefix tailTrace_4251237
  have hstable : (prefixWord ++ tailWord_4251237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251237).length < 2 ^ (prefixWord ++ tailWord_4251237).sum := by decide
  have hdescent : baseEnd_4251237 < baseStart_4251237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251267 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 5, 2, 2]
def baseStart_4251267 : Nat := 118140960795 + 4251267 * 2 ^ 59
def prefixEnd_4251267 : Nat := 4983230072969 + 3 ^ 40 * 4251267 * 2
def baseEnd_4251267 : Nat := 2182943361597723632011285

theorem tailTrace_4251267 : CollatzResearch.WordTrace tailWord_4251267 prefixEnd_4251267 2182943361597723632011285 := by
  unfold tailWord_4251267
  simp only [CollatzResearch.WordTrace]
  refine ⟨155056445889393192444232055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103370963926262128296154703 155056445889393192444232055)
  ·
    refine ⟨232584668834089788666348083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155056445889393192444232055 232584668834089788666348083)
    ·
      refine ⟨348877003251134682999522125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232584668834089788666348083 348877003251134682999522125)
      ·
        refine ⟨130828876219175506124820797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348877003251134682999522125 130828876219175506124820797)
        ·
          refine ⟨49060828582190814796807799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130828876219175506124820797 49060828582190814796807799)
          ·
            refine ⟨73591242873286222195211699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49060828582190814796807799 73591242873286222195211699)
            ·
              refine ⟨110386864309929333292817549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73591242873286222195211699 110386864309929333292817549)
              ·
                refine ⟨41395074116223499984806581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110386864309929333292817549 41395074116223499984806581)
                ·
                  refine ⟨3880788198395953123575617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41395074116223499984806581 3880788198395953123575617)
                  ·
                    refine ⟨2910591148796964842681713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880788198395953123575617 2910591148796964842681713)
                    ·
                      refine ⟨2182943361597723632011285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910591148796964842681713 2182943361597723632011285)
                      ·
                        rfl

theorem cell23_4251267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_4251267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251267 prefixEnd_4251267 := by exact prefixLift 4251267
  have htrace : WordTrace (prefixWord ++ tailWord_4251267) baseStart_4251267 baseEnd_4251267 := by
    simpa [prefixWord, tailWord_4251267, baseEnd_4251267] using wordTrace_append hprefix tailTrace_4251267
  have hstable : (prefixWord ++ tailWord_4251267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251267).length < 2 ^ (prefixWord ++ tailWord_4251267).sum := by decide
  have hdescent : baseEnd_4251267 < baseStart_4251267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251273 : List Nat := [1, 2, 1, 1, 4, 1, 4, 9]
def baseStart_4251273 : Nat := 118140960795 + 4251273 * 2 ^ 59
def prefixEnd_4251273 : Nat := 4983230072969 + 3 ^ 40 * 4251273 * 2
def baseEnd_4251273 : Nat := 80849868240061133649491

theorem tailTrace_4251273 : CollatzResearch.WordTrace tailWord_4251273 prefixEnd_4251273 80849868240061133649491 := by
  unfold tailWord_4251273
  simp only [CollatzResearch.WordTrace]
  refine ⟨155056664727371455468950473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103371109818247636979300315 155056664727371455468950473)
  ·
    refine ⟨116292498545528591601712855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155056664727371455468950473 116292498545528591601712855)
    ·
      refine ⟨174438747818292887402569283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116292498545528591601712855 174438747818292887402569283)
      ·
        refine ⟨261658121727439331103853925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174438747818292887402569283 261658121727439331103853925)
        ·
          refine ⟨49060897823894874581972611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261658121727439331103853925 49060897823894874581972611)
          ·
            refine ⟨73591346735842311872958917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49060897823894874581972611 73591346735842311872958917)
            ·
              refine ⟨13798377512970433476179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73591346735842311872958917 13798377512970433476179797)
              ·
                refine ⟨80849868240061133649491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13798377512970433476179797 80849868240061133649491)
                ·
                  rfl

theorem cell23_4251273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 9].length) (baseStart_4251273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251273 prefixEnd_4251273 := by exact prefixLift 4251273
  have htrace : WordTrace (prefixWord ++ tailWord_4251273) baseStart_4251273 baseEnd_4251273 := by
    simpa [prefixWord, tailWord_4251273, baseEnd_4251273] using wordTrace_append hprefix tailTrace_4251273
  have hstable : (prefixWord ++ tailWord_4251273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251273).length < 2 ^ (prefixWord ++ tailWord_4251273).sum := by decide
  have hdescent : baseEnd_4251273 < baseStart_4251273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251287 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_4251287 : Nat := 118140960795 + 4251287 * 2 ^ 59
def prefixEnd_4251287 : Nat := 4983230072969 + 3 ^ 40 * 4251287 * 2
def baseEnd_4251287 : Nat := 2182953631210813553761193

theorem tailTrace_4251287 : CollatzResearch.WordTrace tailWord_4251287 prefixEnd_4251287 2182953631210813553761193 := by
  unfold tailWord_4251287
  simp only [CollatzResearch.WordTrace]
  refine ⟨155057175349320735859960115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103371450232880490573306743 155057175349320735859960115)
  ·
    refine ⟨232585763023981103789940173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155057175349320735859960115 232585763023981103789940173)
    ·
      refine ⟨87219661133992913921227565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232585763023981103789940173 87219661133992913921227565)
      ·
        refine ⟨32707372925247342720460337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87219661133992913921227565 32707372925247342720460337)
        ·
          refine ⟨24530529693935507040345253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32707372925247342720460337 24530529693935507040345253)
          ·
            refine ⟨4599474317612907570064735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24530529693935507040345253 4599474317612907570064735)
            ·
              refine ⟨6899211476419361355097103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599474317612907570064735 6899211476419361355097103)
              ·
                refine ⟨10348817214629042032645655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899211476419361355097103 10348817214629042032645655)
                ·
                  refine ⟨15523225821943563048968483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10348817214629042032645655 15523225821943563048968483)
                  ·
                    refine ⟨23284838732915344573452725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15523225821943563048968483 23284838732915344573452725)
                    ·
                      refine ⟨2182953631210813553761193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23284838732915344573452725 2182953631210813553761193)
                      ·
                        rfl

theorem cell23_4251287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_4251287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251287 prefixEnd_4251287 := by exact prefixLift 4251287
  have htrace : WordTrace (prefixWord ++ tailWord_4251287) baseStart_4251287 baseEnd_4251287 := by
    simpa [prefixWord, tailWord_4251287, baseEnd_4251287] using wordTrace_append hprefix tailTrace_4251287
  have hstable : (prefixWord ++ tailWord_4251287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251287).length < 2 ^ (prefixWord ++ tailWord_4251287).sum := by decide
  have hdescent : baseEnd_4251287 < baseStart_4251287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251294 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4251294 : Nat := 118140960795 + 4251294 * 2 ^ 59
def prefixEnd_4251294 : Nat := 4983230072969 + 3 ^ 40 * 4251294 * 2
def baseEnd_4251294 : Nat := 727652408525131675457887

theorem tailTrace_4251294 : CollatzResearch.WordTrace tailWord_4251294 prefixEnd_4251294 727652408525131675457887 := by
  unfold tailWord_4251294
  simp only [CollatzResearch.WordTrace]
  refine ⟨19382178832536922006933117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103371620440196917370309957 19382178832536922006933117)
  ·
    refine ⟨7268317062201345752599919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19382178832536922006933117 7268317062201345752599919)
    ·
      refine ⟨10902475593302018628899879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268317062201345752599919 10902475593302018628899879)
      ·
        refine ⟨16353713389953027943349819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902475593302018628899879 16353713389953027943349819)
        ·
          refine ⟨24530570084929541915024729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16353713389953027943349819 24530570084929541915024729)
          ·
            refine ⟨18397927563697156436268547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24530570084929541915024729 18397927563697156436268547)
            ·
              refine ⟨27596891345545734654402821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18397927563697156436268547 27596891345545734654402821)
              ·
                refine ⟨5174417127289825247700529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27596891345545734654402821 5174417127289825247700529)
                ·
                  refine ⟨3880812845467368935775397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5174417127289825247700529 3880812845467368935775397)
                  ·
                    refine ⟨727652408525131675457887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880812845467368935775397 727652408525131675457887)
                    ·
                      rfl

theorem cell23_4251294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4251294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251294 prefixEnd_4251294 := by exact prefixLift 4251294
  have htrace : WordTrace (prefixWord ++ tailWord_4251294) baseStart_4251294 baseEnd_4251294 := by
    simpa [prefixWord, tailWord_4251294, baseEnd_4251294] using wordTrace_append hprefix tailTrace_4251294
  have hstable : (prefixWord ++ tailWord_4251294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251294).length < 2 ^ (prefixWord ++ tailWord_4251294).sum := by decide
  have hdescent : baseEnd_4251294 < baseStart_4251294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251295 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4251295 : Nat := 118140960795 + 4251295 * 2 ^ 59
def prefixEnd_4251295 : Nat := 4983230072969 + 3 ^ 40 * 4251295 * 2
def baseEnd_4251295 : Nat := 2182957739056049522461157

theorem tailTrace_4251295 : CollatzResearch.WordTrace tailWord_4251295 prefixEnd_4251295 2182957739056049522461157 := by
  unfold tailWord_4251295
  simp only [CollatzResearch.WordTrace]
  refine ⟨155057467133291753226251339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103371644755527835484167559 155057467133291753226251339)
  ·
    refine ⟨232586200699937629839377009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155057467133291753226251339 232586200699937629839377009)
    ·
      refine ⟨174439650524953222379532757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232586200699937629839377009 174439650524953222379532757)
      ·
        refine ⟨4088429309178591149520299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 174439650524953222379532757 4088429309178591149520299)
        ·
          refine ⟨6132643963767886724280449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088429309178591149520299 6132643963767886724280449)
          ·
            refine ⟨4599482972825915043210337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132643963767886724280449 4599482972825915043210337)
            ·
              refine ⟨3449612229619436282407753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599482972825915043210337 3449612229619436282407753)
              ·
                refine ⟨2587209172214577211805815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3449612229619436282407753 2587209172214577211805815)
                ·
                  refine ⟨3880813758321865817708723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587209172214577211805815 3880813758321865817708723)
                  ·
                    refine ⟨5821220637482798726563085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3880813758321865817708723 5821220637482798726563085)
                    ·
                      refine ⟨2182957739056049522461157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5821220637482798726563085 2182957739056049522461157)
                      ·
                        rfl

theorem cell23_4251295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4251295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251295 prefixEnd_4251295 := by exact prefixLift 4251295
  have htrace : WordTrace (prefixWord ++ tailWord_4251295) baseStart_4251295 baseEnd_4251295 := by
    simpa [prefixWord, tailWord_4251295, baseEnd_4251295] using wordTrace_append hprefix tailTrace_4251295
  have hstable : (prefixWord ++ tailWord_4251295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251295).length < 2 ^ (prefixWord ++ tailWord_4251295).sum := by decide
  have hdescent : baseEnd_4251295 < baseStart_4251295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251318 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4251318 : Nat := 118140960795 + 4251318 * 2 ^ 59
def prefixEnd_4251318 : Nat := 4983230072969 + 3 ^ 40 * 4251318 * 2
def baseEnd_4251318 : Nat := 2182969549111102932473551

theorem tailTrace_4251318 : CollatzResearch.WordTrace tailWord_4251318 prefixEnd_4251318 2182969549111102932473551 := by
  unfold tailWord_4251318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691144125763026759646163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103372204008138952102892405 9691144125763026759646163)
  ·
    refine ⟨14536716188644540139469245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691144125763026759646163 14536716188644540139469245)
    ·
      refine ⟨5451268570741702552300967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14536716188644540139469245 5451268570741702552300967)
      ·
        refine ⟨8176902856112553828451451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451268570741702552300967 8176902856112553828451451)
        ·
          refine ⟨12265354284168830742677177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8176902856112553828451451 12265354284168830742677177)
          ·
            refine ⟨9199015713126623057007883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12265354284168830742677177 9199015713126623057007883)
            ·
              refine ⟨13798523569689934585511825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199015713126623057007883 13798523569689934585511825)
              ·
                refine ⟨10348892677267450939133869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13798523569689934585511825 10348892677267450939133869)
                ·
                  refine ⟨3880834753975294102175201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10348892677267450939133869 3880834753975294102175201)
                  ·
                    refine ⟨2910626065481470576631401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880834753975294102175201 2910626065481470576631401)
                    ·
                      refine ⟨2182969549111102932473551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910626065481470576631401 2182969549111102932473551)
                      ·
                        rfl

theorem cell23_4251318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4251318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251318 prefixEnd_4251318 := by exact prefixLift 4251318
  have htrace : WordTrace (prefixWord ++ tailWord_4251318) baseStart_4251318 baseEnd_4251318 := by
    simpa [prefixWord, tailWord_4251318, baseEnd_4251318] using wordTrace_append hprefix tailTrace_4251318
  have hstable : (prefixWord ++ tailWord_4251318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251318).length < 2 ^ (prefixWord ++ tailWord_4251318).sum := by decide
  have hdescent : baseEnd_4251318 < baseStart_4251318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251327 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 3, 3, 2]
def baseStart_4251327 : Nat := 118140960795 + 4251327 * 2 ^ 59
def prefixEnd_4251327 : Nat := 4983230072969 + 3 ^ 40 * 4251327 * 2
def baseEnd_4251327 : Nat := 2182974170436993397261009

theorem tailTrace_4251327 : CollatzResearch.WordTrace tailWord_4251327 prefixEnd_4251327 2182974170436993397261009 := by
  unfold tailWord_4251327
  simp only [CollatzResearch.WordTrace]
  refine ⟨155058634269175822691416235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103372422846117215127610823 155058634269175822691416235)
  ·
    refine ⟨232587951403763734037124353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155058634269175822691416235 232587951403763734037124353)
    ·
      refine ⟨174440963552822800527843265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232587951403763734037124353 174440963552822800527843265)
      ·
        refine ⟨130830722664617100395882449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174440963552822800527843265 130830722664617100395882449)
        ·
          refine ⟨98123041998462825296911837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130830722664617100395882449 98123041998462825296911837)
          ·
            refine ⟨36796140749423559486341939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98123041998462825296911837 36796140749423559486341939)
            ·
              refine ⟨55194211124135339229512909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36796140749423559486341939 55194211124135339229512909)
              ·
                refine ⟨20697829171550752211067341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55194211124135339229512909 20697829171550752211067341)
                ·
                  refine ⟨7761685939331532079150253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20697829171550752211067341 7761685939331532079150253)
                  ·
                    refine ⟨2910632227249324529681345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7761685939331532079150253 2910632227249324529681345)
                    ·
                      refine ⟨2182974170436993397261009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910632227249324529681345 2182974170436993397261009)
                      ·
                        rfl

theorem cell23_4251327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_4251327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251327 prefixEnd_4251327 := by exact prefixLift 4251327
  have htrace : WordTrace (prefixWord ++ tailWord_4251327) baseStart_4251327 baseEnd_4251327 := by
    simpa [prefixWord, tailWord_4251327, baseEnd_4251327] using wordTrace_append hprefix tailTrace_4251327
  have hstable : (prefixWord ++ tailWord_4251327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251327).length < 2 ^ (prefixWord ++ tailWord_4251327).sum := by decide
  have hdescent : baseEnd_4251327 < baseStart_4251327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251338 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_4251338 : Nat := 118140960795 + 4251338 * 2 ^ 59
def prefixEnd_4251338 : Nat := 4983230072969 + 3 ^ 40 * 4251338 * 2
def baseEnd_4251338 : Nat := 2182979818724192854223459

theorem tailTrace_4251338 : CollatzResearch.WordTrace tailWord_4251338 prefixEnd_4251338 2182979818724192854223459 := by
  unfold tailWord_4251338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38764758868033992892516667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103372690314757314380044445 38764758868033992892516667)
  ·
    refine ⟨58147138302050989338775001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38764758868033992892516667 58147138302050989338775001)
    ·
      refine ⟨43610353726538242004081251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58147138302050989338775001 43610353726538242004081251)
      ·
        refine ⟨65415530589807363006121877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43610353726538242004081251 65415530589807363006121877)
        ·
          refine ⟨3066352996397220140911963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65415530589807363006121877 3066352996397220140911963)
          ·
            refine ⟨4599529494595830211367945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066352996397220140911963 4599529494595830211367945)
            ·
              refine ⟨3449647120946872658525959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599529494595830211367945 3449647120946872658525959)
              ·
                refine ⟨5174470681420308987788939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449647120946872658525959 5174470681420308987788939)
                ·
                  refine ⟨7761706022130463481683409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174470681420308987788939 7761706022130463481683409)
                  ·
                    refine ⟨5821279516597847611262557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7761706022130463481683409 5821279516597847611262557)
                    ·
                      refine ⟨2182979818724192854223459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5821279516597847611262557 2182979818724192854223459)
                      ·
                        rfl

theorem cell23_4251338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_4251338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251338 prefixEnd_4251338 := by exact prefixLift 4251338
  have htrace : WordTrace (prefixWord ++ tailWord_4251338) baseStart_4251338 baseEnd_4251338 := by
    simpa [prefixWord, tailWord_4251338, baseEnd_4251338] using wordTrace_append hprefix tailTrace_4251338
  have hstable : (prefixWord ++ tailWord_4251338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251338).length < 2 ^ (prefixWord ++ tailWord_4251338).sum := by decide
  have hdescent : baseEnd_4251338 < baseStart_4251338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251360 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_4251360 : Nat := 118140960795 + 4251360 * 2 ^ 59
def prefixEnd_4251360 : Nat := 4983230072969 + 3 ^ 40 * 4251360 * 2
def baseEnd_4251360 : Nat := 2182991115298591768148357

theorem tailTrace_4251360 : CollatzResearch.WordTrace tailWord_4251360 prefixEnd_4251360 2182991115298591768148357 := by
  unfold tailWord_4251360
  simp only [CollatzResearch.WordTrace]
  refine ⟨77529918939028134663683767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103373225252037512884911689 77529918939028134663683767)
  ·
    refine ⟨116294878408542201995525651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77529918939028134663683767 116294878408542201995525651)
    ·
      refine ⟨174442317612813302993288477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116294878408542201995525651 174442317612813302993288477)
      ·
        refine ⟨65415869104804988622483179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174442317612813302993288477 65415869104804988622483179)
        ·
          refine ⟨98123803657207482933724769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65415869104804988622483179 98123803657207482933724769)
          ·
            refine ⟨73592852742905612200293577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98123803657207482933724769 73592852742905612200293577)
            ·
              refine ⟨55194639557179209150220183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73592852742905612200293577 55194639557179209150220183)
              ·
                refine ⟨82791959335768813725330275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55194639557179209150220183 82791959335768813725330275)
                ·
                  refine ⟨124187939003653220587995413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82791959335768813725330275 124187939003653220587995413)
                  ·
                    refine ⟨5821309640796244715062285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124187939003653220587995413 5821309640796244715062285)
                    ·
                      refine ⟨2182991115298591768148357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5821309640796244715062285 2182991115298591768148357)
                      ·
                        rfl

theorem cell23_4251360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_4251360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251360 prefixEnd_4251360 := by exact prefixLift 4251360
  have htrace : WordTrace (prefixWord ++ tailWord_4251360) baseStart_4251360 baseEnd_4251360 := by
    simpa [prefixWord, tailWord_4251360, baseEnd_4251360] using wordTrace_append hprefix tailTrace_4251360
  have hstable : (prefixWord ++ tailWord_4251360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251360).length < 2 ^ (prefixWord ++ tailWord_4251360).sum := by decide
  have hdescent : baseEnd_4251360 < baseStart_4251360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251444 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4251444 : Nat := 118140960795 + 4251444 * 2 ^ 59
def prefixEnd_4251444 : Nat := 4983230072969 + 3 ^ 40 * 4251444 * 2
def baseEnd_4251444 : Nat := 727678082557856479832657

theorem tailTrace_4251444 : CollatzResearch.WordTrace tailWord_4251444 prefixEnd_4251444 727678082557856479832657 := by
  unfold tailWord_4251444
  simp only [CollatzResearch.WordTrace]
  refine ⟨77531450804875975836712693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103375267739834634448950257 77531450804875975836712693)
  ·
    refine ⟨7268573512957122734691815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77531450804875975836712693 7268573512957122734691815)
    ·
      refine ⟨10902860269435684102037723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268573512957122734691815 10902860269435684102037723)
      ·
        refine ⟨16354290404153526153056585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902860269435684102037723 16354290404153526153056585)
        ·
          refine ⟨12265717803115144614792439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16354290404153526153056585 12265717803115144614792439)
          ·
            refine ⟨18398576704672716922188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12265717803115144614792439 18398576704672716922188659)
            ·
              refine ⟨27597865057009075383282989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18398576704672716922188659 27597865057009075383282989)
              ·
                refine ⟨10349199396378403268731121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27597865057009075383282989 10349199396378403268731121)
                ·
                  refine ⟨7761899547283802451548341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10349199396378403268731121 7761899547283802451548341)
                  ·
                    refine ⟨727678082557856479832657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7761899547283802451548341 727678082557856479832657)
                    ·
                      rfl

theorem cell23_4251444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4251444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251444 prefixEnd_4251444 := by exact prefixLift 4251444
  have htrace : WordTrace (prefixWord ++ tailWord_4251444) baseStart_4251444 baseEnd_4251444 := by
    simpa [prefixWord, tailWord_4251444, baseEnd_4251444] using wordTrace_append hprefix tailTrace_4251444
  have hstable : (prefixWord ++ tailWord_4251444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251444).length < 2 ^ (prefixWord ++ tailWord_4251444).sum := by decide
  have hdescent : baseEnd_4251444 < baseStart_4251444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251447 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_4251447 : Nat := 118140960795 + 4251447 * 2 ^ 59
def prefixEnd_4251447 : Nat := 4983230072969 + 3 ^ 40 * 4251447 * 2
def baseEnd_4251447 : Nat := 2183035788115532927760457

theorem tailTrace_4251447 : CollatzResearch.WordTrace tailWord_4251447 prefixEnd_4251447 2183035788115532927760457 := by
  unfold tailWord_4251447
  simp only [CollatzResearch.WordTrace]
  refine ⟨155063011028741083185784595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103375340685827388790523063 155063011028741083185784595)
  ·
    refine ⟨232594516543111624778676893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155063011028741083185784595 232594516543111624778676893)
    ·
      refine ⟨87222943703666859292003835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232594516543111624778676893 87222943703666859292003835)
      ·
        refine ⟨130834415555500288938005753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87222943703666859292003835 130834415555500288938005753)
        ·
          refine ⟨98125811666625216703504315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130834415555500288938005753 98125811666625216703504315)
          ·
            refine ⟨147188717499937825055256473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98125811666625216703504315 147188717499937825055256473)
            ·
              refine ⟨110391538124953368791442355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147188717499937825055256473 110391538124953368791442355)
              ·
                refine ⟨165587307187430053187163533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110391538124953368791442355 165587307187430053187163533)
                ·
                  refine ⟨62095240195286269945186325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165587307187430053187163533 62095240195286269945186325)
                  ·
                    refine ⟨2910714384154043903680609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62095240195286269945186325 2910714384154043903680609)
                    ·
                      refine ⟨2183035788115532927760457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910714384154043903680609 2183035788115532927760457)
                      ·
                        rfl

theorem cell23_4251447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_4251447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251447 prefixEnd_4251447 := by exact prefixLift 4251447
  have htrace : WordTrace (prefixWord ++ tailWord_4251447) baseStart_4251447 baseEnd_4251447 := by
    simpa [prefixWord, tailWord_4251447, baseEnd_4251447] using wordTrace_append hprefix tailTrace_4251447
  have hstable : (prefixWord ++ tailWord_4251447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251447).length < 2 ^ (prefixWord ++ tailWord_4251447).sum := by decide
  have hdescent : baseEnd_4251447 < baseStart_4251447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251487 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 6]
def baseStart_4251487 : Nat := 118140960795 + 4251487 * 2 ^ 59
def prefixEnd_4251487 : Nat := 4983230072969 + 3 ^ 40 * 4251487 * 2
def baseEnd_4251487 : Nat := 242561814149079196806697

theorem tailTrace_4251487 : CollatzResearch.WordTrace tailWord_4251487 prefixEnd_4251487 242561814149079196806697 := by
  unfold tailWord_4251487
  simp only [CollatzResearch.WordTrace]
  refine ⟨155064469948596170017240715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103376313299064113344827143 155064469948596170017240715)
  ·
    refine ⟨232596704922894255025861073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155064469948596170017240715 232596704922894255025861073)
    ·
      refine ⟨174447528692170691269395805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232596704922894255025861073 174447528692170691269395805)
      ·
        refine ⟨65417823259564009226023427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174447528692170691269395805 65417823259564009226023427)
        ·
          refine ⟨98126734889346013839035141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65417823259564009226023427 98126734889346013839035141)
          ·
            refine ⟨18398762791752377594819089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98126734889346013839035141 18398762791752377594819089)
            ·
              refine ⟨13799072093814283196114317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18398762791752377594819089 13799072093814283196114317)
              ·
                refine ⟨5174652035180356198542869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13799072093814283196114317 5174652035180356198542869)
                ·
                  refine ⟨242561814149079196806697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5174652035180356198542869 242561814149079196806697)
                  ·
                    rfl

theorem cell23_4251487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 6].length) (baseStart_4251487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251487 prefixEnd_4251487 := by exact prefixLift 4251487
  have htrace : WordTrace (prefixWord ++ tailWord_4251487) baseStart_4251487 baseEnd_4251487 := by
    simpa [prefixWord, tailWord_4251487, baseEnd_4251487] using wordTrace_append hprefix tailTrace_4251487
  have hstable : (prefixWord ++ tailWord_4251487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251487).length < 2 ^ (prefixWord ++ tailWord_4251487).sum := by decide
  have hdescent : baseEnd_4251487 < baseStart_4251487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251498 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4251498 : Nat := 118140960795 + 4251498 * 2 ^ 59
def prefixEnd_4251498 : Nat := 4983230072969 + 3 ^ 40 * 4251498 * 2
def baseEnd_4251498 : Nat := 2183061975628912228222723

theorem tailTrace_4251498 : CollatzResearch.WordTrace tailWord_4251498 prefixEnd_4251498 2183061975628912228222723 := by
  unfold tailWord_4251498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766217787889079723972787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103376580767704212597260765 38766217787889079723972787)
  ·
    refine ⟨58149326681833619585959181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38766217787889079723972787 58149326681833619585959181)
    ·
      refine ⟨21805997505687607344734693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58149326681833619585959181 21805997505687607344734693)
      ·
        refine ⟨4088624532316426377137755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21805997505687607344734693 4088624532316426377137755)
        ·
          refine ⟨6132936798474639565706633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088624532316426377137755 6132936798474639565706633)
          ·
            refine ⟨4599702598855979674279975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132936798474639565706633 4599702598855979674279975)
            ·
              refine ⟨6899553898283969511419963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599702598855979674279975 6899553898283969511419963)
              ·
                refine ⟨10349330847425954267129945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899553898283969511419963 10349330847425954267129945)
                ·
                  refine ⟨7761998135569465700347459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10349330847425954267129945 7761998135569465700347459)
                  ·
                    refine ⟨11642997203354198550521189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7761998135569465700347459 11642997203354198550521189)
                    ·
                      refine ⟨2183061975628912228222723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11642997203354198550521189 2183061975628912228222723)
                      ·
                        rfl

theorem cell23_4251498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4251498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251498 prefixEnd_4251498 := by exact prefixLift 4251498
  have htrace : WordTrace (prefixWord ++ tailWord_4251498) baseStart_4251498 baseEnd_4251498 := by
    simpa [prefixWord, tailWord_4251498, baseEnd_4251498] using wordTrace_append hprefix tailTrace_4251498
  have hstable : (prefixWord ++ tailWord_4251498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251498).length < 2 ^ (prefixWord ++ tailWord_4251498).sum := by decide
  have hdescent : baseEnd_4251498 < baseStart_4251498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251537 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_4251537 : Nat := 118140960795 + 4251537 * 2 ^ 59
def prefixEnd_4251537 : Nat := 4983230072969 + 3 ^ 40 * 4251537 * 2
def baseEnd_4251537 : Nat := 2183082001374437575635043

theorem tailTrace_4251537 : CollatzResearch.WordTrace tailWord_4251537 prefixEnd_4251537 2183082001374437575635043 := by
  unfold tailWord_4251537
  simp only [CollatzResearch.WordTrace]
  refine ⟨155066293598415028556560865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103377529065610019037707243 155066293598415028556560865)
  ·
    refine ⟨116299720198811271417420649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155066293598415028556560865 116299720198811271417420649)
    ·
      refine ⟨87224790149108453563065487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116299720198811271417420649 87224790149108453563065487)
      ·
        refine ⟨130837185223662680344598231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87224790149108453563065487 130837185223662680344598231)
        ·
          refine ⟨196255777835494020516897347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130837185223662680344598231 196255777835494020516897347)
          ·
            refine ⟨294383666753241030775346021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196255777835494020516897347 294383666753241030775346021)
            ·
              refine ⟨55196937516232693270377379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294383666753241030775346021 55196937516232693270377379)
              ·
                refine ⟨82795406274349039905566069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55196937516232693270377379 82795406274349039905566069)
                ·
                  refine ⟨7762069338220222491146819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82795406274349039905566069 7762069338220222491146819)
                  ·
                    refine ⟨11643104007330333736720229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7762069338220222491146819 11643104007330333736720229)
                    ·
                      refine ⟨2183082001374437575635043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643104007330333736720229 2183082001374437575635043)
                      ·
                        rfl

theorem cell23_4251537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_4251537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251537 prefixEnd_4251537 := by exact prefixLift 4251537
  have htrace : WordTrace (prefixWord ++ tailWord_4251537) baseStart_4251537 baseEnd_4251537 := by
    simpa [prefixWord, tailWord_4251537, baseEnd_4251537] using wordTrace_append hprefix tailTrace_4251537
  have hstable : (prefixWord ++ tailWord_4251537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251537).length < 2 ^ (prefixWord ++ tailWord_4251537).sum := by decide
  have hdescent : baseEnd_4251537 < baseStart_4251537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251551 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 1, 5]
def baseStart_4251551 : Nat := 118140960795 + 4251551 * 2 ^ 59
def prefixEnd_4251551 : Nat := 4983230072969 + 3 ^ 40 * 4251551 * 2
def baseEnd_4251551 : Nat := 727696396701200173619993

theorem tailTrace_4251551 : CollatzResearch.WordTrace tailWord_4251551 prefixEnd_4251551 727696396701200173619993 := by
  unfold tailWord_4251551
  simp only [CollatzResearch.WordTrace]
  refine ⟨155066804220364308947570507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103377869480242872631713671 155066804220364308947570507)
  ·
    refine ⟨232600206330546463421355761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155066804220364308947570507 232600206330546463421355761)
    ·
      refine ⟨174450154747909847566016821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232600206330546463421355761 174450154747909847566016821)
      ·
        refine ⟨16354702007616548209314077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174450154747909847566016821 16354702007616548209314077)
        ·
          refine ⟨6133013252856205578492779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16354702007616548209314077 6133013252856205578492779)
          ·
            refine ⟨9199519879284308367739169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133013252856205578492779 9199519879284308367739169)
            ·
              refine ⟨6899639909463231275804377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9199519879284308367739169 6899639909463231275804377)
              ·
                refine ⟨5174729932097423456853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6899639909463231275804377 5174729932097423456853283)
                ·
                  refine ⟨7762094898146135185279925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174729932097423456853283 7762094898146135185279925)
                  ·
                    refine ⟨727696396701200173619993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7762094898146135185279925 727696396701200173619993)
                    ·
                      rfl

theorem cell23_4251551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_4251551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251551 prefixEnd_4251551 := by exact prefixLift 4251551
  have htrace : WordTrace (prefixWord ++ tailWord_4251551) baseStart_4251551 baseEnd_4251551 := by
    simpa [prefixWord, tailWord_4251551, baseEnd_4251551] using wordTrace_append hprefix tailTrace_4251551
  have hstable : (prefixWord ++ tailWord_4251551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251551).length < 2 ^ (prefixWord ++ tailWord_4251551).sum := by decide
  have hdescent : baseEnd_4251551 < baseStart_4251551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251557 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_4251557 : Nat := 118140960795 + 4251557 * 2 ^ 59
def prefixEnd_4251557 : Nat := 4983230072969 + 3 ^ 40 * 4251557 * 2
def baseEnd_4251557 : Nat := 2183092270987527497384951

theorem tailTrace_4251557 : CollatzResearch.WordTrace tailWord_4251557 prefixEnd_4251557 2183092270987527497384951 := by
  unfold tailWord_4251557
  simp only [CollatzResearch.WordTrace]
  refine ⟨155067023058342571972288925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103378015372228381314859283 155067023058342571972288925)
  ·
    refine ⟨58150133646878464489608347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155067023058342571972288925 58150133646878464489608347)
    ·
      refine ⟨87225200470317696734412521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58150133646878464489608347 87225200470317696734412521)
      ·
        refine ⟨65418900352738272550809391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87225200470317696734412521 65418900352738272550809391)
        ·
          refine ⟨98128350529107408826214087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65418900352738272550809391 98128350529107408826214087)
          ·
            refine ⟨147192525793661113239321131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98128350529107408826214087 147192525793661113239321131)
            ·
              refine ⟨220788788690491669858981697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147192525793661113239321131 220788788690491669858981697)
              ·
                refine ⟨165591591517868752394236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220788788690491669858981697 165591591517868752394236273)
                ·
                  refine ⟨124193693638401564295677205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165591591517868752394236273 124193693638401564295677205)
                  ·
                    refine ⟨5821579389300073326359869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124193693638401564295677205 5821579389300073326359869)
                    ·
                      refine ⟨2183092270987527497384951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5821579389300073326359869 2183092270987527497384951)
                      ·
                        rfl

theorem cell23_4251557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_4251557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251557 prefixEnd_4251557 := by exact prefixLift 4251557
  have htrace : WordTrace (prefixWord ++ tailWord_4251557) baseStart_4251557 baseEnd_4251557 := by
    simpa [prefixWord, tailWord_4251557, baseEnd_4251557] using wordTrace_append hprefix tailTrace_4251557
  have hstable : (prefixWord ++ tailWord_4251557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251557).length < 2 ^ (prefixWord ++ tailWord_4251557).sum := by decide
  have hdescent : baseEnd_4251557 < baseStart_4251557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251567 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_4251567 : Nat := 118140960795 + 4251567 * 2 ^ 59
def prefixEnd_4251567 : Nat := 4983230072969 + 3 ^ 40 * 4251567 * 2
def baseEnd_4251567 : Nat := 2183097405794072458259905

theorem tailTrace_4251567 : CollatzResearch.WordTrace tailWord_4251567 prefixEnd_4251567 2183097405794072458259905 := by
  unfold tailWord_4251567
  simp only [CollatzResearch.WordTrace]
  refine ⟨155067387788306343680152955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103378258525537562453435303 155067387788306343680152955)
  ·
    refine ⟨232601081682459515520229433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155067387788306343680152955 232601081682459515520229433)
    ·
      refine ⟨174450811261844636640172075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232601081682459515520229433 174450811261844636640172075)
      ·
        refine ⟨261676216892766954960258113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174450811261844636640172075 261676216892766954960258113)
        ·
          refine ⟨196257162669575216220193585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261676216892766954960258113 196257162669575216220193585)
          ·
            refine ⟨147192872002181412165145189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196257162669575216220193585 147192872002181412165145189)
            ·
              refine ⟨27598663500409014780964723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147192872002181412165145189 27598663500409014780964723)
              ·
                refine ⟨41397995250613522171447085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27598663500409014780964723 41397995250613522171447085)
                ·
                  refine ⟨15524248218980070814292657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41397995250613522171447085 15524248218980070814292657)
                  ·
                    refine ⟨11643186164235053110719493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15524248218980070814292657 11643186164235053110719493)
                    ·
                      refine ⟨2183097405794072458259905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643186164235053110719493 2183097405794072458259905)
                      ·
                        rfl

theorem cell23_4251567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_4251567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251567 prefixEnd_4251567 := by exact prefixLift 4251567
  have htrace : WordTrace (prefixWord ++ tailWord_4251567) baseStart_4251567 baseEnd_4251567 := by
    simpa [prefixWord, tailWord_4251567, baseEnd_4251567] using wordTrace_append hprefix tailTrace_4251567
  have hstable : (prefixWord ++ tailWord_4251567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251567).length < 2 ^ (prefixWord ++ tailWord_4251567).sum := by decide
  have hdescent : baseEnd_4251567 < baseStart_4251567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251587 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3]
def baseStart_4251587 : Nat := 118140960795 + 4251587 * 2 ^ 59
def prefixEnd_4251587 : Nat := 4983230072969 + 3 ^ 40 * 4251587 * 2
def baseEnd_4251587 : Nat := 2183107675407162380009813

theorem tailTrace_4251587 : CollatzResearch.WordTrace tailWord_4251587 prefixEnd_4251587 2183107675407162380009813 := by
  unfold tailWord_4251587
  simp only [CollatzResearch.WordTrace]
  refine ⟨155068117248233887095881015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103378744832155924730587343 155068117248233887095881015)
  ·
    refine ⟨232602175872350830643821523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155068117248233887095881015 232602175872350830643821523)
    ·
      refine ⟨348903263808526245965732285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232602175872350830643821523 348903263808526245965732285)
      ·
        refine ⟨130838723928197342237149607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348903263808526245965732285 130838723928197342237149607)
        ·
          refine ⟨196258085892296013355724411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130838723928197342237149607 196258085892296013355724411)
          ·
            refine ⟨294387128838444020033586617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196258085892296013355724411 294387128838444020033586617)
            ·
              refine ⟨220790346628833015025189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294387128838444020033586617 220790346628833015025189963)
              ·
                refine ⟨331185519943249522537784945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220790346628833015025189963 331185519943249522537784945)
                ·
                  refine ⟨248389139957437141903338709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331185519943249522537784945 248389139957437141903338709)
                  ·
                    refine ⟨5821620467752433013359501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 248389139957437141903338709 5821620467752433013359501)
                    ·
                      refine ⟨2183107675407162380009813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5821620467752433013359501 2183107675407162380009813)
                      ·
                        rfl

theorem cell23_4251587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_4251587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251587 prefixEnd_4251587 := by exact prefixLift 4251587
  have htrace : WordTrace (prefixWord ++ tailWord_4251587) baseStart_4251587 baseEnd_4251587 := by
    simpa [prefixWord, tailWord_4251587, baseEnd_4251587] using wordTrace_append hprefix tailTrace_4251587
  have hstable : (prefixWord ++ tailWord_4251587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251587).length < 2 ^ (prefixWord ++ tailWord_4251587).sum := by decide
  have hdescent : baseEnd_4251587 < baseStart_4251587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251617 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4251617 : Nat := 118140960795 + 4251617 * 2 ^ 59
def prefixEnd_4251617 : Nat := 4983230072969 + 3 ^ 40 * 4251617 * 2
def baseEnd_4251617 : Nat := 2183123079826797262634675

theorem tailTrace_4251617 : CollatzResearch.WordTrace tailWord_4251617 prefixEnd_4251617 2183123079826797262634675 := by
  unfold tailWord_4251617
  simp only [CollatzResearch.WordTrace]
  refine ⟨155069211438125202219473105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103379474292083468146315403 155069211438125202219473105)
  ·
    refine ⟨116301908578593901664604829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155069211438125202219473105 116301908578593901664604829)
    ·
      refine ⟨43613215716972713124226811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116301908578593901664604829 43613215716972713124226811)
      ·
        refine ⟨65419823575459069686340217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43613215716972713124226811 65419823575459069686340217)
        ·
          refine ⟨49064867681594302264755163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65419823575459069686340217 49064867681594302264755163)
          ·
            refine ⟨73597301522391453397132745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49064867681594302264755163 73597301522391453397132745)
            ·
              refine ⟨55197976141793590047849559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73597301522391453397132745 55197976141793590047849559)
              ·
                refine ⟨82796964212690385071774339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55197976141793590047849559 82796964212690385071774339)
                ·
                  refine ⟨124195446319035577607661509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82796964212690385071774339 124195446319035577607661509)
                  ·
                    refine ⟨23286646184819170801436533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124195446319035577607661509 23286646184819170801436533)
                    ·
                      refine ⟨2183123079826797262634675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23286646184819170801436533 2183123079826797262634675)
                      ·
                        rfl

theorem cell23_4251617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4251617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251617 prefixEnd_4251617 := by exact prefixLift 4251617
  have htrace : WordTrace (prefixWord ++ tailWord_4251617) baseStart_4251617 baseEnd_4251617 := by
    simpa [prefixWord, tailWord_4251617, baseEnd_4251617] using wordTrace_append hprefix tailTrace_4251617
  have hstable : (prefixWord ++ tailWord_4251617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251617).length < 2 ^ (prefixWord ++ tailWord_4251617).sum := by decide
  have hdescent : baseEnd_4251617 < baseStart_4251617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251618 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4251618 : Nat := 118140960795 + 4251618 * 2 ^ 59
def prefixEnd_4251618 : Nat := 4983230072969 + 3 ^ 40 * 4251618 * 2
def baseEnd_4251618 : Nat := 2183123593307451758722171

theorem tailTrace_4251618 : CollatzResearch.WordTrace tailWord_4251618 prefixEnd_4251618 2183123593307451758722171 := by
  unfold tailWord_4251618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38767311977780394847564877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103379498607414386260173005 38767311977780394847564877)
  ·
    refine ⟨14537741991667648067836829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38767311977780394847564877 14537741991667648067836829)
    ·
      refine ⟨5451653246875368025438811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14537741991667648067836829 5451653246875368025438811)
      ·
        refine ⟨8177479870313052038158217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451653246875368025438811 8177479870313052038158217)
        ·
          refine ⟨6133109902734789028618663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177479870313052038158217 6133109902734789028618663)
          ·
            refine ⟨9199664854102183542927995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133109902734789028618663 9199664854102183542927995)
            ·
              refine ⟨13799497281153275314391993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199664854102183542927995 13799497281153275314391993)
              ·
                refine ⟨10349622960864956485793995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13799497281153275314391993 10349622960864956485793995)
                ·
                  refine ⟨15524434441297434728690993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10349622960864956485793995 15524434441297434728690993)
                  ·
                    refine ⟨11643325830973076046518245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15524434441297434728690993 11643325830973076046518245)
                    ·
                      refine ⟨2183123593307451758722171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643325830973076046518245 2183123593307451758722171)
                      ·
                        rfl

theorem cell23_4251618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4251618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251618 prefixEnd_4251618 := by exact prefixLift 4251618
  have htrace : WordTrace (prefixWord ++ tailWord_4251618) baseStart_4251618 baseEnd_4251618 := by
    simpa [prefixWord, tailWord_4251618, baseEnd_4251618] using wordTrace_append hprefix tailTrace_4251618
  have hstable : (prefixWord ++ tailWord_4251618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251618).length < 2 ^ (prefixWord ++ tailWord_4251618).sum := by decide
  have hdescent : baseEnd_4251618 < baseStart_4251618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251627 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_4251627 : Nat := 118140960795 + 4251627 * 2 ^ 59
def prefixEnd_4251627 : Nat := 4983230072969 + 3 ^ 40 * 4251627 * 2
def baseEnd_4251627 : Nat := 2183128214633342223509629

theorem tailTrace_4251627 : CollatzResearch.WordTrace tailWord_4251627 prefixEnd_4251627 2183128214633342223509629 := by
  unfold tailWord_4251627
  simp only [CollatzResearch.WordTrace]
  refine ⟨155069576168088973927337135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103379717445392649284891423 155069576168088973927337135)
  ·
    refine ⟨232604364252133460891005703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155069576168088973927337135 232604364252133460891005703)
    ·
      refine ⟨348906546378200191336508555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232604364252133460891005703 348906546378200191336508555)
      ·
        refine ⟨523359819567300287004762833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348906546378200191336508555 523359819567300287004762833)
        ·
          refine ⟨392519864675475215253572125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523359819567300287004762833 392519864675475215253572125)
          ·
            refine ⟨147194949253303205720089547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392519864675475215253572125 147194949253303205720089547)
            ·
              refine ⟨220792423879954808580134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147194949253303205720089547 220792423879954808580134321)
              ·
                refine ⟨165594317909966106435100741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220792423879954808580134321 165594317909966106435100741)
                ·
                  refine ⟨31048934608118644956581389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165594317909966106435100741 31048934608118644956581389)
                  ·
                    refine ⟨11643350478044491858718021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31048934608118644956581389 11643350478044491858718021)
                    ·
                      refine ⟨2183128214633342223509629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643350478044491858718021 2183128214633342223509629)
                      ·
                        rfl

theorem cell23_4251627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_4251627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251627 prefixEnd_4251627 := by exact prefixLift 4251627
  have htrace : WordTrace (prefixWord ++ tailWord_4251627) baseStart_4251627 baseEnd_4251627 := by
    simpa [prefixWord, tailWord_4251627, baseEnd_4251627] using wordTrace_append hprefix tailTrace_4251627
  have hstable : (prefixWord ++ tailWord_4251627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251627).length < 2 ^ (prefixWord ++ tailWord_4251627).sum := by decide
  have hdescent : baseEnd_4251627 < baseStart_4251627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251647 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_4251647 : Nat := 118140960795 + 4251647 * 2 ^ 59
def prefixEnd_4251647 : Nat := 4983230072969 + 3 ^ 40 * 4251647 * 2
def baseEnd_4251647 : Nat := 2183138484246432145259537

theorem tailTrace_4251647 : CollatzResearch.WordTrace tailWord_4251647 prefixEnd_4251647 2183138484246432145259537 := by
  unfold tailWord_4251647
  simp only [CollatzResearch.WordTrace]
  refine ⟨155070305628016517343065195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103380203752011011562043463 155070305628016517343065195)
  ·
    refine ⟨232605458442024776014597793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155070305628016517343065195 232605458442024776014597793)
    ·
      refine ⟨174454093831518582010948345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232605458442024776014597793 174454093831518582010948345)
      ·
        refine ⟨130840570373638936508211259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174454093831518582010948345 130840570373638936508211259)
        ·
          refine ⟨196260855560458404762316889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130840570373638936508211259 196260855560458404762316889)
          ·
            refine ⟨147195641670343803571737667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196260855560458404762316889 147195641670343803571737667)
            ·
              refine ⟨220793462505515705357606501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147195641670343803571737667 220793462505515705357606501)
              ·
                refine ⟨41398774219784194754551219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220793462505515705357606501 41398774219784194754551219)
                ·
                  refine ⟨62098161329676292131826829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41398774219784194754551219 62098161329676292131826829)
                  ·
                    refine ⟨23286810498628609549435061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62098161329676292131826829 23286810498628609549435061)
                    ·
                      refine ⟨2183138484246432145259537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23286810498628609549435061 2183138484246432145259537)
                      ·
                        rfl

theorem cell23_4251647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_4251647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251647 prefixEnd_4251647 := by exact prefixLift 4251647
  have htrace : WordTrace (prefixWord ++ tailWord_4251647) baseStart_4251647 baseEnd_4251647 := by
    simpa [prefixWord, tailWord_4251647, baseEnd_4251647] using wordTrace_append hprefix tailTrace_4251647
  have hstable : (prefixWord ++ tailWord_4251647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251647).length < 2 ^ (prefixWord ++ tailWord_4251647).sum := by decide
  have hdescent : baseEnd_4251647 < baseStart_4251647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251667 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 9]
def baseStart_4251667 : Nat := 118140960795 + 4251667 * 2 ^ 59
def prefixEnd_4251667 : Nat := 4983230072969 + 3 ^ 40 * 4251667 * 2
def baseEnd_4251667 : Nat := 242572083762169118556605

theorem tailTrace_4251667 : CollatzResearch.WordTrace tailWord_4251667 prefixEnd_4251667 242572083762169118556605 := by
  unfold tailWord_4251667
  simp only [CollatzResearch.WordTrace]
  refine ⟨155071035087944060758793255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103380690058629373839195503 155071035087944060758793255)
  ·
    refine ⟨232606552631916091138189883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155071035087944060758793255 232606552631916091138189883)
    ·
      refine ⟨348909828947874136707284825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232606552631916091138189883 348909828947874136707284825)
      ·
        refine ⟨261682371710905602530463619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348909828947874136707284825 261682371710905602530463619)
        ·
          refine ⟨392523557566358403795695429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261682371710905602530463619 392523557566358403795695429)
          ·
            refine ⟨73598167043692200711692893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 392523557566358403795695429 73598167043692200711692893)
            ·
              refine ⟨27599312641384575266884835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73598167043692200711692893 27599312641384575266884835)
              ·
                refine ⟨41398968962076862900327253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27599312641384575266884835 41398968962076862900327253)
                ·
                  refine ⟨242572083762169118556605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41398968962076862900327253 242572083762169118556605)
                  ·
                    rfl

theorem cell23_4251667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 9].length) (baseStart_4251667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251667 prefixEnd_4251667 := by exact prefixLift 4251667
  have htrace : WordTrace (prefixWord ++ tailWord_4251667) baseStart_4251667 baseEnd_4251667 := by
    simpa [prefixWord, tailWord_4251667, baseEnd_4251667] using wordTrace_append hprefix tailTrace_4251667
  have hstable : (prefixWord ++ tailWord_4251667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251667).length < 2 ^ (prefixWord ++ tailWord_4251667).sum := by decide
  have hdescent : baseEnd_4251667 < baseStart_4251667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251701 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 5]
def baseStart_4251701 : Nat := 118140960795 + 4251701 * 2 ^ 59
def prefixEnd_4251701 : Nat := 4983230072969 + 3 ^ 40 * 4251701 * 2
def baseEnd_4251701 : Nat := 242574023577974992664921

theorem tailTrace_4251701 : CollatzResearch.WordTrace tailWord_4251701 prefixEnd_4251701 242574023577974992664921 := by
  unfold tailWord_4251701
  simp only [CollatzResearch.WordTrace]
  refine ⟨155072275169820884565530957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103381516779880589710353971 155072275169820884565530957)
  ·
    refine ⟨58152103188682831712074109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155072275169820884565530957 58152103188682831712074109)
    ·
      refine ⟨21807038695756061892027791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58152103188682831712074109 21807038695756061892027791)
      ·
        refine ⟨32710558043634092838041687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21807038695756061892027791 32710558043634092838041687)
        ·
          refine ⟨49065837065451139257062531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32710558043634092838041687 49065837065451139257062531)
          ·
            refine ⟨73598755598176708885593797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49065837065451139257062531 73598755598176708885593797)
            ·
              refine ⟨13799766674658132916048837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73598755598176708885593797 13799766674658132916048837)
              ·
                refine ⟨2587456251498399921759157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13799766674658132916048837 2587456251498399921759157)
                ·
                  refine ⟨242574023577974992664921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2587456251498399921759157 242574023577974992664921)
                  ·
                    rfl

theorem cell23_4251701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_4251701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251701 prefixEnd_4251701 := by exact prefixLift 4251701
  have htrace : WordTrace (prefixWord ++ tailWord_4251701) baseStart_4251701 baseEnd_4251701 := by
    simpa [prefixWord, tailWord_4251701, baseEnd_4251701] using wordTrace_append hprefix tailTrace_4251701
  have hstable : (prefixWord ++ tailWord_4251701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251701).length < 2 ^ (prefixWord ++ tailWord_4251701).sum := by decide
  have hdescent : baseEnd_4251701 < baseStart_4251701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251751 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4251751 : Nat := 118140960795 + 4251751 * 2 ^ 59
def prefixEnd_4251751 : Nat := 4983230072969 + 3 ^ 40 * 4251751 * 2
def baseEnd_4251751 : Nat := 2183191886234499738359059

theorem tailTrace_4251751 : CollatzResearch.WordTrace tailWord_4251751 prefixEnd_4251751 2183191886234499738359059 := by
  unfold tailWord_4251751
  simp only [CollatzResearch.WordTrace]
  refine ⟨155074098819639743104851107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103382732546426495403234071 155074098819639743104851107)
  ·
    refine ⟨232611148229459614657276661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155074098819639743104851107 232611148229459614657276661)
    ·
      refine ⟨21807295146511838874119687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232611148229459614657276661 21807295146511838874119687)
      ·
        refine ⟨32710942719767758311179531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21807295146511838874119687 32710942719767758311179531)
        ·
          refine ⟨49066414079651637466769297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32710942719767758311179531 49066414079651637466769297)
          ·
            refine ⟨36799810559738728100076973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49066414079651637466769297 36799810559738728100076973)
            ·
              refine ⟨13799928959902023037528865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36799810559738728100076973 13799928959902023037528865)
              ·
                refine ⟨10349946719926517278146649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13799928959902023037528865 10349946719926517278146649)
                ·
                  refine ⟨7762460039944887958609987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10349946719926517278146649 7762460039944887958609987)
                  ·
                    refine ⟨11643690059917331937914981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7762460039944887958609987 11643690059917331937914981)
                    ·
                      refine ⟨2183191886234499738359059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643690059917331937914981 2183191886234499738359059)
                      ·
                        rfl

theorem cell23_4251751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4251751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251751 prefixEnd_4251751 := by exact prefixLift 4251751
  have htrace : WordTrace (prefixWord ++ tailWord_4251751) baseStart_4251751 baseEnd_4251751 := by
    simpa [prefixWord, tailWord_4251751, baseEnd_4251751] using wordTrace_append hprefix tailTrace_4251751
  have hstable : (prefixWord ++ tailWord_4251751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251751).length < 2 ^ (prefixWord ++ tailWord_4251751).sum := by decide
  have hdescent : baseEnd_4251751 < baseStart_4251751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251811 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 5, 2]
def baseStart_4251811 : Nat := 118140960795 + 4251811 * 2 ^ 59
def prefixEnd_4251811 : Nat := 4983230072969 + 3 ^ 40 * 4251811 * 2
def baseEnd_4251811 : Nat := 2183222695073769503608783

theorem tailTrace_4251811 : CollatzResearch.WordTrace tailWord_4251811 prefixEnd_4251811 2183222695073769503608783 := by
  unfold tailWord_4251811
  simp only [CollatzResearch.WordTrace]
  refine ⟨155076287199422373352035287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103384191466281582234690191 155076287199422373352035287)
  ·
    refine ⟨232614430799133560028052931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155076287199422373352035287 232614430799133560028052931)
    ·
      refine ⟨348921646198700340042079397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232614430799133560028052931 348921646198700340042079397)
      ·
        refine ⟨65422808662256313757889887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348921646198700340042079397 65422808662256313757889887)
        ·
          refine ⟨98134212993384470636834831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65422808662256313757889887 98134212993384470636834831)
          ·
            refine ⟨147201319490076705955252247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98134212993384470636834831 147201319490076705955252247)
            ·
              refine ⟨220801979235115058932878371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147201319490076705955252247 220801979235115058932878371)
              ·
                refine ⟨331202968852672588399317557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220801979235115058932878371 331202968852672588399317557)
                ·
                  refine ⟨31050278329938055162436021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331202968852672588399317557 31050278329938055162436021)
                  ·
                    refine ⟨2910963593431692671478377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31050278329938055162436021 2910963593431692671478377)
                    ·
                      refine ⟨2183222695073769503608783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910963593431692671478377 2183222695073769503608783)
                      ·
                        rfl

theorem cell23_4251811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_4251811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251811 prefixEnd_4251811 := by exact prefixLift 4251811
  have htrace : WordTrace (prefixWord ++ tailWord_4251811) baseStart_4251811 baseEnd_4251811 := by
    simpa [prefixWord, tailWord_4251811, baseEnd_4251811] using wordTrace_append hprefix tailTrace_4251811
  have hstable : (prefixWord ++ tailWord_4251811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251811).length < 2 ^ (prefixWord ++ tailWord_4251811).sum := by decide
  have hdescent : baseEnd_4251811 < baseStart_4251811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251824 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_4251824 : Nat := 118140960795 + 4251824 * 2 ^ 59
def prefixEnd_4251824 : Nat := 4983230072969 + 3 ^ 40 * 4251824 * 2
def baseEnd_4251824 : Nat := 2183229370322277952746223

theorem tailTrace_4251824 : CollatzResearch.WordTrace tailWord_4251824 prefixEnd_4251824 2183229370322277952746223 := by
  unfold tailWord_4251824
  simp only [CollatzResearch.WordTrace]
  refine ⟨77538380674187638286129263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103384507565583517714839017 77538380674187638286129263)
  ·
    refine ⟨116307571011281457429193895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77538380674187638286129263 116307571011281457429193895)
    ·
      refine ⟨174461356516922186143790843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116307571011281457429193895 174461356516922186143790843)
      ·
        refine ⟨261692034775383279215686265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174461356516922186143790843 261692034775383279215686265)
        ·
          refine ⟨196269026081537459411764699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261692034775383279215686265 196269026081537459411764699)
          ·
            refine ⟨294403539122306189117647049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196269026081537459411764699 294403539122306189117647049)
            ·
              refine ⟨220802654341729641838235287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294403539122306189117647049 220802654341729641838235287)
              ·
                refine ⟨331203981512594462757352931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220802654341729641838235287 331203981512594462757352931)
                ·
                  refine ⟨496805972268891694136029397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331203981512594462757352931 496805972268891694136029397)
                  ·
                    refine ⟨11643889975052149081313189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 496805972268891694136029397 11643889975052149081313189)
                    ·
                      refine ⟨2183229370322277952746223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11643889975052149081313189 2183229370322277952746223)
                      ·
                        rfl

theorem cell23_4251824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_4251824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251824 prefixEnd_4251824 := by exact prefixLift 4251824
  have htrace : WordTrace (prefixWord ++ tailWord_4251824) baseStart_4251824 baseEnd_4251824 := by
    simpa [prefixWord, tailWord_4251824, baseEnd_4251824] using wordTrace_append hprefix tailTrace_4251824
  have hstable : (prefixWord ++ tailWord_4251824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251824).length < 2 ^ (prefixWord ++ tailWord_4251824).sum := by decide
  have hdescent : baseEnd_4251824 < baseStart_4251824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251851 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 4, 4]
def baseStart_4251851 : Nat := 118140960795 + 4251851 * 2 ^ 59
def prefixEnd_4251851 : Nat := 4983230072969 + 3 ^ 40 * 4251851 * 2
def baseEnd_4251851 : Nat := 727747744766649782369533

theorem tailTrace_4251851 : CollatzResearch.WordTrace tailWord_4251851 prefixEnd_4251851 727747744766649782369533 := by
  unfold tailWord_4251851
  simp only [CollatzResearch.WordTrace]
  refine ⟨155077746119277460183491407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103385164079518306788994271 155077746119277460183491407)
  ·
    refine ⟨232616619178916190275237111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155077746119277460183491407 232616619178916190275237111)
    ·
      refine ⟨348924928768374285412855667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232616619178916190275237111 348924928768374285412855667)
      ·
        refine ⟨523387393152561428119283501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348924928768374285412855667 523387393152561428119283501)
        ·
          refine ⟨196270272432210535544731313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523387393152561428119283501 196270272432210535544731313)
          ·
            refine ⟨147202704324157901658548485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196270272432210535544731313 147202704324157901658548485)
            ·
              refine ⟨27600507060779606560977841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147202704324157901658548485 27600507060779606560977841)
              ·
                refine ⟨20700380295584704920733381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27600507060779606560977841 20700380295584704920733381)
                ·
                  refine ⟨3881321305422132172637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20700380295584704920733381 3881321305422132172637509)
                  ·
                    refine ⟨727747744766649782369533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881321305422132172637509 727747744766649782369533)
                    ·
                      rfl

theorem cell23_4251851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 4].length) (baseStart_4251851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251851 prefixEnd_4251851 := by exact prefixLift 4251851
  have htrace : WordTrace (prefixWord ++ tailWord_4251851) baseStart_4251851 baseEnd_4251851 := by
    simpa [prefixWord, tailWord_4251851, baseEnd_4251851] using wordTrace_append hprefix tailTrace_4251851
  have hstable : (prefixWord ++ tailWord_4251851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251851).length < 2 ^ (prefixWord ++ tailWord_4251851).sum := by decide
  have hdescent : baseEnd_4251851 < baseStart_4251851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251885 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4251885 : Nat := 118140960795 + 4251885 * 2 ^ 59
def prefixEnd_4251885 : Nat := 4983230072969 + 3 ^ 40 * 4251885 * 2
def baseEnd_4251885 : Nat := 727753564214067404694481

theorem tailTrace_4251885 : CollatzResearch.WordTrace tailWord_4251885 prefixEnd_4251885 727753564214067404694481 := by
  unfold tailWord_4251885
  simp only [CollatzResearch.WordTrace]
  refine ⟨155078986201154283990229109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103385990800769522660152739 155078986201154283990229109)
  ·
    refine ⟨14538654956358214124083979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 155078986201154283990229109 14538654956358214124083979)
    ·
      refine ⟨21807982434537321186125969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14538654956358214124083979 21807982434537321186125969)
      ·
        refine ⟨16355986825902990889594477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21807982434537321186125969 16355986825902990889594477)
        ·
          refine ⟨6133495059713621583597929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16355986825902990889594477 6133495059713621583597929)
          ·
            refine ⟨4600121294785216187698447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6133495059713621583597929 4600121294785216187698447)
            ·
              refine ⟨6900181942177824281547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600121294785216187698447 6900181942177824281547671)
              ·
                refine ⟨10350272913266736422321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6900181942177824281547671 10350272913266736422321507)
                ·
                  refine ⟨15525409369900104633482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10350272913266736422321507 15525409369900104633482261)
                  ·
                    refine ⟨727753564214067404694481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15525409369900104633482261 727753564214067404694481)
                    ·
                      rfl

theorem cell23_4251885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4251885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251885 prefixEnd_4251885 := by exact prefixLift 4251885
  have htrace : WordTrace (prefixWord ++ tailWord_4251885) baseStart_4251885 baseEnd_4251885 := by
    simpa [prefixWord, tailWord_4251885, baseEnd_4251885] using wordTrace_append hprefix tailTrace_4251885
  have hstable : (prefixWord ++ tailWord_4251885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251885).length < 2 ^ (prefixWord ++ tailWord_4251885).sum := by decide
  have hdescent : baseEnd_4251885 < baseStart_4251885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251898 : List Nat := [3, 1, 1, 1, 1, 7, 2, 7]
def baseStart_4251898 : Nat := 118140960795 + 4251898 * 2 ^ 59
def prefixEnd_4251898 : Nat := 4983230072969 + 3 ^ 40 * 4251898 * 2
def baseEnd_4251898 : Nat := 80861754366322617156329

theorem tailTrace_4251898 : CollatzResearch.WordTrace tailWord_4251898 prefixEnd_4251898 80861754366322617156329 := by
  unfold tailWord_4251898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38769865087526796802613087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103386306900071458140301565 38769865087526796802613087)
  ·
    refine ⟨58154797631290195203919631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38769865087526796802613087 58154797631290195203919631)
    ·
      refine ⟨87232196446935292805879447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58154797631290195203919631 87232196446935292805879447)
      ·
        refine ⟨130848294670402939208819171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87232196446935292805879447 130848294670402939208819171)
        ·
          refine ⟨196272442005604408813228757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130848294670402939208819171 196272442005604408813228757)
          ·
            refine ⟨4600135359506353331560049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 196272442005604408813228757 4600135359506353331560049)
            ·
              refine ⟨3450101519629764998670037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600135359506353331560049 3450101519629764998670037)
              ·
                refine ⟨80861754366322617156329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3450101519629764998670037 80861754366322617156329)
                ·
                  rfl

theorem cell23_4251898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_4251898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251898 prefixEnd_4251898 := by exact prefixLift 4251898
  have htrace : WordTrace (prefixWord ++ tailWord_4251898) baseStart_4251898 baseEnd_4251898 := by
    simpa [prefixWord, tailWord_4251898, baseEnd_4251898] using wordTrace_append hprefix tailTrace_4251898
  have hstable : (prefixWord ++ tailWord_4251898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251898).length < 2 ^ (prefixWord ++ tailWord_4251898).sum := by decide
  have hdescent : baseEnd_4251898 < baseStart_4251898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251951 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_4251951 : Nat := 118140960795 + 4251951 * 2 ^ 59
def prefixEnd_4251951 : Nat := 4983230072969 + 3 ^ 40 * 4251951 * 2
def baseEnd_4251951 : Nat := 2183294582365398955858139

theorem tailTrace_4251951 : CollatzResearch.WordTrace tailWord_4251951 prefixEnd_4251951 2183294582365398955858139 := by
  unfold tailWord_4251951
  simp only [CollatzResearch.WordTrace]
  refine ⟨155081393418915177262131707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103387595612610118174754471 155081393418915177262131707)
  ·
    refine ⟨232622090128372765893197561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155081393418915177262131707 232622090128372765893197561)
    ·
      refine ⟨174466567596279574419898171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232622090128372765893197561 174466567596279574419898171)
      ·
        refine ⟨261699851394419361629847257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174466567596279574419898171 261699851394419361629847257)
        ·
          refine ⟨196274888545814521222385443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261699851394419361629847257 196274888545814521222385443)
          ·
            refine ⟨294412332818721781833578165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196274888545814521222385443 294412332818721781833578165)
            ·
              refine ⟨27601156201755167046897953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 294412332818721781833578165 27601156201755167046897953)
              ·
                refine ⟨20700867151316375285173465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27601156201755167046897953 20700867151316375285173465)
                ·
                  refine ⟨15525650363487281463880099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20700867151316375285173465 15525650363487281463880099)
                  ·
                    refine ⟨23288475545230922195820149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15525650363487281463880099 23288475545230922195820149)
                    ·
                      refine ⟨2183294582365398955858139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23288475545230922195820149 2183294582365398955858139)
                      ·
                        rfl

theorem cell23_4251951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_4251951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251951 prefixEnd_4251951 := by exact prefixLift 4251951
  have htrace : WordTrace (prefixWord ++ tailWord_4251951) baseStart_4251951 baseEnd_4251951 := by
    simpa [prefixWord, tailWord_4251951, baseEnd_4251951] using wordTrace_append hprefix tailTrace_4251951
  have hstable : (prefixWord ++ tailWord_4251951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251951).length < 2 ^ (prefixWord ++ tailWord_4251951).sum := by decide
  have hdescent : baseEnd_4251951 < baseStart_4251951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252018 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_4252018 : Nat := 118140960795 + 4252018 * 2 ^ 59
def prefixEnd_4252018 : Nat := 4983230072969 + 3 ^ 40 * 4252018 * 2
def baseEnd_4252018 : Nat := 727776328523083397906777

theorem tailTrace_4252018 : CollatzResearch.WordTrace tailWord_4252018 prefixEnd_4252018 727776328523083397906777 := by
  unfold tailWord_4252018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38770959277418111926205177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103389224739781631803213805 38770959277418111926205177)
  ·
    refine ⟨29078219458063583944653883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38770959277418111926205177 29078219458063583944653883)
    ·
      refine ⟨43617329187095375916980825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29078219458063583944653883 43617329187095375916980825)
      ·
        refine ⟨32712996890321531937735619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43617329187095375916980825 32712996890321531937735619)
        ·
          refine ⟨49069495335482297906603429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32712996890321531937735619 49069495335482297906603429)
          ·
            refine ⟨9200530375402930857488143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49069495335482297906603429 9200530375402930857488143)
            ·
              refine ⟨13800795563104396286232215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9200530375402930857488143 13800795563104396286232215)
              ·
                refine ⟨20701193344656594429348323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13800795563104396286232215 20701193344656594429348323)
                ·
                  refine ⟨31051790016984891644022485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20701193344656594429348323 31051790016984891644022485)
                  ·
                    refine ⟨727776328523083397906777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31051790016984891644022485 727776328523083397906777)
                    ·
                      rfl

theorem cell23_4252018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_4252018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252018 prefixEnd_4252018 := by exact prefixLift 4252018
  have htrace : WordTrace (prefixWord ++ tailWord_4252018) baseStart_4252018 baseEnd_4252018 := by
    simpa [prefixWord, tailWord_4252018, baseEnd_4252018] using wordTrace_append hprefix tailTrace_4252018
  have hstable : (prefixWord ++ tailWord_4252018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252018).length < 2 ^ (prefixWord ++ tailWord_4252018).sum := by decide
  have hdescent : baseEnd_4252018 < baseStart_4252018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252055 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_4252055 : Nat := 118140960795 + 4252055 * 2 ^ 59
def prefixEnd_4252055 : Nat := 4983230072969 + 3 ^ 40 * 4252055 * 2
def baseEnd_4252055 : Nat := 2183347984353466548957661

theorem tailTrace_4252055 : CollatzResearch.WordTrace tailWord_4252055 prefixEnd_4252055 2183347984353466548957661 := by
  unfold tailWord_4252055
  simp only [CollatzResearch.WordTrace]
  refine ⟨155085186610538403023917619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103390124407025602015945079 155085186610538403023917619)
  ·
    refine ⟨232627779915807604535876429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155085186610538403023917619 232627779915807604535876429)
    ·
      refine ⟨87235417468427851700953661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232627779915807604535876429 87235417468427851700953661)
      ·
        refine ⟨32713281550660444387857623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87235417468427851700953661 32713281550660444387857623)
        ·
          refine ⟨49069922325990666581786435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32713281550660444387857623 49069922325990666581786435)
          ·
            refine ⟨73604883488985999872679653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49069922325990666581786435 73604883488985999872679653)
            ·
              refine ⟨13800915654184874976127435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73604883488985999872679653 13800915654184874976127435)
              ·
                refine ⟨20701373481277312464191153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13800915654184874976127435 20701373481277312464191153)
                ·
                  refine ⟨15526030110957984348143365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20701373481277312464191153 15526030110957984348143365)
                  ·
                    refine ⟨2911130645804622065276881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15526030110957984348143365 2911130645804622065276881)
                    ·
                      refine ⟨2183347984353466548957661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911130645804622065276881 2183347984353466548957661)
                      ·
                        rfl

theorem cell23_4252055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_4252055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252055 prefixEnd_4252055 := by exact prefixLift 4252055
  have htrace : WordTrace (prefixWord ++ tailWord_4252055) baseStart_4252055 baseEnd_4252055 := by
    simpa [prefixWord, tailWord_4252055, baseEnd_4252055] using wordTrace_append hprefix tailTrace_4252055
  have hstable : (prefixWord ++ tailWord_4252055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252055).length < 2 ^ (prefixWord ++ tailWord_4252055).sum := by decide
  have hdescent : baseEnd_4252055 < baseStart_4252055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252092 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4252092 : Nat := 118140960795 + 4252092 * 2 ^ 59
def prefixEnd_4252092 : Nat := 4983230072969 + 3 ^ 40 * 4252092 * 2
def baseEnd_4252092 : Nat := 2183366983137682904194991

theorem tailTrace_4252092 : CollatzResearch.WordTrace tailWord_4252092 prefixEnd_4252092 2183366983137682904194991 := by
  unfold tailWord_4252092
  simp only [CollatzResearch.WordTrace]
  refine ⟨77543268055702179171507265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103391024074269572228676353 77543268055702179171507265)
  ·
    refine ⟨58157451041776634378630449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77543268055702179171507265 58157451041776634378630449)
    ·
      refine ⟨43618088281332475783972837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58157451041776634378630449 43618088281332475783972837)
      ·
        refine ⟨8178391552749839209494907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43618088281332475783972837 8178391552749839209494907)
        ·
          refine ⟨12267587329124758814242361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8178391552749839209494907 12267587329124758814242361)
          ·
            refine ⟨9200690496843569110681771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12267587329124758814242361 9200690496843569110681771)
            ·
              refine ⟨13801035745265353666022657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9200690496843569110681771 13801035745265353666022657)
              ·
                refine ⟨10350776808949015249516993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13801035745265353666022657 10350776808949015249516993)
                ·
                  refine ⟨7763082606711761437137745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10350776808949015249516993 7763082606711761437137745)
                  ·
                    refine ⟨5822311955033821077853309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7763082606711761437137745 5822311955033821077853309)
                    ·
                      refine ⟨2183366983137682904194991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5822311955033821077853309 2183366983137682904194991)
                      ·
                        rfl

theorem cell23_4252092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4252092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252092 prefixEnd_4252092 := by exact prefixLift 4252092
  have htrace : WordTrace (prefixWord ++ tailWord_4252092) baseStart_4252092 baseEnd_4252092 := by
    simpa [prefixWord, tailWord_4252092, baseEnd_4252092] using wordTrace_append hprefix tailTrace_4252092
  have hstable : (prefixWord ++ tailWord_4252092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252092).length < 2 ^ (prefixWord ++ tailWord_4252092).sum := by decide
  have hdescent : baseEnd_4252092 < baseStart_4252092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252125 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4252125 : Nat := 118140960795 + 4252125 * 2 ^ 59
def prefixEnd_4252125 : Nat := 4983230072969 + 3 ^ 40 * 4252125 * 2
def baseEnd_4252125 : Nat := 727794642666427091694113

theorem tailTrace_4252125 : CollatzResearch.WordTrace tailWord_4252125 prefixEnd_4252125 727794642666427091694113 := by
  unfold tailWord_4252125
  simp only [CollatzResearch.WordTrace]
  refine ⟨155087739720284804978965829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103391826480189869985977219 155087739720284804978965829)
  ·
    refine ⟨29078951197553400933556093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155087739720284804978965829 29078951197553400933556093)
    ·
      refine ⟨10904606699082525350083535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29078951197553400933556093 10904606699082525350083535)
      ·
        refine ⟨16356910048623788025125303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10904606699082525350083535 16356910048623788025125303)
        ·
          refine ⟨24535365072935682037687955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16356910048623788025125303 24535365072935682037687955)
          ·
            refine ⟨36803047609403523056531933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24535365072935682037687955 36803047609403523056531933)
            ·
              refine ⟨13801142853526321146199475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36803047609403523056531933 13801142853526321146199475)
              ·
                refine ⟨20701714280289481719299213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13801142853526321146199475 20701714280289481719299213)
                ·
                  refine ⟨7763142855108555644737205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20701714280289481719299213 7763142855108555644737205)
                  ·
                    refine ⟨727794642666427091694113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7763142855108555644737205 727794642666427091694113)
                    ·
                      rfl

theorem cell23_4252125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4252125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252125 prefixEnd_4252125 := by exact prefixLift 4252125
  have htrace : WordTrace (prefixWord ++ tailWord_4252125) baseStart_4252125 baseEnd_4252125 := by
    simpa [prefixWord, tailWord_4252125, baseEnd_4252125] using wordTrace_append hprefix tailTrace_4252125
  have hstable : (prefixWord ++ tailWord_4252125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252125).length < 2 ^ (prefixWord ++ tailWord_4252125).sum := by decide
  have hdescent : baseEnd_4252125 < baseStart_4252125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252165 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_4252165 : Nat := 118140960795 + 4252165 * 2 ^ 59
def prefixEnd_4252165 : Nat := 4983230072969 + 3 ^ 40 * 4252165 * 2
def baseEnd_4252165 : Nat := 2183404467225461118582155

theorem tailTrace_4252165 : CollatzResearch.WordTrace tailWord_4252165 prefixEnd_4252165 2183404467225461118582155 := by
  unfold tailWord_4252165
  simp only [CollatzResearch.WordTrace]
  refine ⟨155089198640139891810421949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103392799093426594540281299 155089198640139891810421949)
  ·
    refine ⟨58158449490052459428908231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155089198640139891810421949 58158449490052459428908231)
    ·
      refine ⟨87237674235078689143362347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58158449490052459428908231 87237674235078689143362347)
      ·
        refine ⟨130856511352618033715043521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87237674235078689143362347 130856511352618033715043521)
        ·
          refine ⟨98142383514463525286282641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130856511352618033715043521 98142383514463525286282641)
          ·
            refine ⟨73606787635847643964711981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98142383514463525286282641 73606787635847643964711981)
            ·
              refine ⟨27602545363442866486766993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73606787635847643964711981 27602545363442866486766993)
              ·
                refine ⟨20701909022582149865075245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27602545363442866486766993 20701909022582149865075245)
                ·
                  refine ⟨7763215883468306199403217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20701909022582149865075245 7763215883468306199403217)
                  ·
                    refine ⟨5822411912601229649552413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7763215883468306199403217 5822411912601229649552413)
                    ·
                      refine ⟨2183404467225461118582155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5822411912601229649552413 2183404467225461118582155)
                      ·
                        rfl

theorem cell23_4252165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_4252165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252165 prefixEnd_4252165 := by exact prefixLift 4252165
  have htrace : WordTrace (prefixWord ++ tailWord_4252165) baseStart_4252165 baseEnd_4252165 := by
    simpa [prefixWord, tailWord_4252165, baseEnd_4252165] using wordTrace_append hprefix tailTrace_4252165
  have hstable : (prefixWord ++ tailWord_4252165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252165).length < 2 ^ (prefixWord ++ tailWord_4252165).sum := by decide
  have hdescent : baseEnd_4252165 < baseStart_4252165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252172 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_4252172 : Nat := 118140960795 + 4252172 * 2 ^ 59
def prefixEnd_4252172 : Nat := 4983230072969 + 3 ^ 40 * 4252172 * 2
def baseEnd_4252172 : Nat := 727802687196680863731541

theorem tailTrace_4252172 : CollatzResearch.WordTrace tailWord_4252172 prefixEnd_4252172 727802687196680863731541 := by
  unfold tailWord_4252172
  simp only [CollatzResearch.WordTrace]
  refine ⟨77544726975557266002963385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103392969300743021337284513 77544726975557266002963385)
  ·
    refine ⟨58158545231667949502222539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77544726975557266002963385 58158545231667949502222539)
    ·
      refine ⟨87237817847501924253333809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58158545231667949502222539 87237817847501924253333809)
      ·
        refine ⟨65428363385626443190000357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87237817847501924253333809 65428363385626443190000357)
        ·
          refine ⟨12267818134804958098125067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65428363385626443190000357 12267818134804958098125067)
          ·
            refine ⟨18401727202207437147187601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12267818134804958098125067 18401727202207437147187601)
            ·
              refine ⟨13801295401655577860390701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18401727202207437147187601 13801295401655577860390701)
              ·
                refine ⟨5175485775620841697646513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13801295401655577860390701 5175485775620841697646513)
                ·
                  refine ⟨3881614331715631273234885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5175485775620841697646513 3881614331715631273234885)
                  ·
                    refine ⟨727802687196680863731541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881614331715631273234885 727802687196680863731541)
                    ·
                      rfl

theorem cell23_4252172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_4252172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252172 prefixEnd_4252172 := by exact prefixLift 4252172
  have htrace : WordTrace (prefixWord ++ tailWord_4252172) baseStart_4252172 baseEnd_4252172 := by
    simpa [prefixWord, tailWord_4252172, baseEnd_4252172] using wordTrace_append hprefix tailTrace_4252172
  have hstable : (prefixWord ++ tailWord_4252172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252172).length < 2 ^ (prefixWord ++ tailWord_4252172).sum := by decide
  have hdescent : baseEnd_4252172 < baseStart_4252172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252183 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4252183 : Nat := 118140960795 + 4252183 * 2 ^ 59
def prefixEnd_4252183 : Nat := 4983230072969 + 3 ^ 40 * 4252183 * 2
def baseEnd_4252183 : Nat := 2183413709877242048157073

theorem tailTrace_4252183 : CollatzResearch.WordTrace tailWord_4252183 prefixEnd_4252183 2183413709877242048157073 := by
  unfold tailWord_4252183
  simp only [CollatzResearch.WordTrace]
  refine ⟨155089855154074680884577203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103393236769383120589718135 155089855154074680884577203)
  ·
    refine ⟨232634782731112021326865805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155089855154074680884577203 232634782731112021326865805)
    ·
      refine ⟨87238043524167007997574677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232634782731112021326865805 87238043524167007997574677)
      ·
        refine ⟨4089283290195328499886313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87238043524167007997574677 4089283290195328499886313)
        ·
          refine ⟨3066962467646496374914735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089283290195328499886313 3066962467646496374914735)
          ·
            refine ⟨4600443701469744562372103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066962467646496374914735 4600443701469744562372103)
            ·
              refine ⟨6900665552204616843558155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600443701469744562372103 6900665552204616843558155)
              ·
                refine ⟨10350998328306925265337233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6900665552204616843558155 10350998328306925265337233)
                ·
                  refine ⟨7763248746230193949002925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10350998328306925265337233 7763248746230193949002925)
                  ·
                    refine ⟨2911218279836322730876097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7763248746230193949002925 2911218279836322730876097)
                    ·
                      refine ⟨2183413709877242048157073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911218279836322730876097 2183413709877242048157073)
                      ·
                        rfl

theorem cell23_4252183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4252183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252183 prefixEnd_4252183 := by exact prefixLift 4252183
  have htrace : WordTrace (prefixWord ++ tailWord_4252183) baseStart_4252183 baseEnd_4252183 := by
    simpa [prefixWord, tailWord_4252183, baseEnd_4252183] using wordTrace_append hprefix tailTrace_4252183
  have hstable : (prefixWord ++ tailWord_4252183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252183).length < 2 ^ (prefixWord ++ tailWord_4252183).sum := by decide
  have hdescent : baseEnd_4252183 < baseStart_4252183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252206 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4252206 : Nat := 118140960795 + 4252206 * 2 ^ 59
def prefixEnd_4252206 : Nat := 4983230072969 + 3 ^ 40 * 4252206 * 2
def baseEnd_4252206 : Nat := 727808506644098486056489

theorem tailTrace_4252206 : CollatzResearch.WordTrace tailWord_4252206 prefixEnd_4252206 727808506644098486056489 := by
  unfold tailWord_4252206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19386336754123919476583059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103393796021994237208442981 19386336754123919476583059)
  ·
    refine ⟨29079505131185879214874589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19386336754123919476583059 29079505131185879214874589)
    ·
      refine ⟨10904814424194704705577971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29079505131185879214874589 10904814424194704705577971)
      ·
        refine ⟨16357221636292057058366957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10904814424194704705577971 16357221636292057058366957)
        ·
          refine ⟨6133958113609521396887609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16357221636292057058366957 6133958113609521396887609)
          ·
            refine ⟨4600468585207141047665707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6133958113609521396887609 4600468585207141047665707)
            ·
              refine ⟨6900702877810711571498561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600468585207141047665707 6900702877810711571498561)
              ·
                refine ⟨5175527158358033678623921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6900702877810711571498561 5175527158358033678623921)
                ·
                  refine ⟨3881645368768525258967941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5175527158358033678623921 3881645368768525258967941)
                  ·
                    refine ⟨727808506644098486056489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881645368768525258967941 727808506644098486056489)
                    ·
                      rfl

theorem cell23_4252206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4252206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252206 prefixEnd_4252206 := by exact prefixLift 4252206
  have htrace : WordTrace (prefixWord ++ tailWord_4252206) baseStart_4252206 baseEnd_4252206 := by
    simpa [prefixWord, tailWord_4252206, baseEnd_4252206] using wordTrace_append hprefix tailTrace_4252206
  have hstable : (prefixWord ++ tailWord_4252206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252206).length < 2 ^ (prefixWord ++ tailWord_4252206).sum := by decide
  have hdescent : baseEnd_4252206 < baseStart_4252206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252290 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4252290 : Nat := 118140960795 + 4252290 * 2 ^ 59
def prefixEnd_4252290 : Nat := 4983230072969 + 3 ^ 40 * 4252290 * 2
def baseEnd_4252290 : Nat := 2183468652307273129519081

theorem tailTrace_4252290 : CollatzResearch.WordTrace tailWord_4252290 prefixEnd_4252290 2183468652307273129519081 := by
  unfold tailWord_4252290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38773439441171759539680581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103395838509791358772481549 38773439441171759539680581)
  ·
    refine ⟨7270019895219704913690109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38773439441171759539680581 7270019895219704913690109)
    ·
      refine ⟨2726257460707389342633791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7270019895219704913690109 2726257460707389342633791)
      ·
        refine ⟨4089386191061084013950687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726257460707389342633791 4089386191061084013950687)
        ·
          refine ⟨6134079286591626020926031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089386191061084013950687 6134079286591626020926031)
          ·
            refine ⟨9201118929887439031389047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134079286591626020926031 9201118929887439031389047)
            ·
              refine ⟨13801678394831158547083571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9201118929887439031389047 13801678394831158547083571)
              ·
                refine ⟨20702517592246737820625357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13801678394831158547083571 20702517592246737820625357)
                ·
                  refine ⟨7763444097092526682734509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20702517592246737820625357 7763444097092526682734509)
                  ·
                    refine ⟨2911291536409697506025441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7763444097092526682734509 2911291536409697506025441)
                    ·
                      refine ⟨2183468652307273129519081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911291536409697506025441 2183468652307273129519081)
                      ·
                        rfl

theorem cell23_4252290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4252290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252290 prefixEnd_4252290 := by exact prefixLift 4252290
  have htrace : WordTrace (prefixWord ++ tailWord_4252290) baseStart_4252290 baseEnd_4252290 := by
    simpa [prefixWord, tailWord_4252290, baseEnd_4252290] using wordTrace_append hprefix tailTrace_4252290
  have hstable : (prefixWord ++ tailWord_4252290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252290).length < 2 ^ (prefixWord ++ tailWord_4252290).sum := by decide
  have hdescent : baseEnd_4252290 < baseStart_4252290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252325 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4252325 : Nat := 118140960795 + 4252325 * 2 ^ 59
def prefixEnd_4252325 : Nat := 4983230072969 + 3 ^ 40 * 4252325 * 2
def baseEnd_4252325 : Nat := 2183486624130180492581419

theorem tailTrace_4252325 : CollatzResearch.WordTrace tailWord_4252325 prefixEnd_4252325 2183486624130180492581419 := by
  unfold tailWord_4252325
  simp only [CollatzResearch.WordTrace]
  refine ⟨155095034319560239136246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103396689546373492757497619 155095034319560239136246429)
  ·
    refine ⟨58160637869835089676092411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155095034319560239136246429 58160637869835089676092411)
    ·
      refine ⟨87240956804752634514138617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58160637869835089676092411 87240956804752634514138617)
      ·
        refine ⟨65430717603564475885603963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87240956804752634514138617 65430717603564475885603963)
        ·
          refine ⟨98146076405346713828405945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65430717603564475885603963 98146076405346713828405945)
          ·
            refine ⟨73609557304010035371304459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98146076405346713828405945 73609557304010035371304459)
            ·
              refine ⟨110414335956015053056956689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73609557304010035371304459 110414335956015053056956689)
              ·
                refine ⟨82810751967011289792717517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110414335956015053056956689 82810751967011289792717517)
                ·
                  refine ⟨31054031987629233672269069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82810751967011289792717517 31054031987629233672269069)
                  ·
                    refine ⟨11645261995360962627100901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31054031987629233672269069 11645261995360962627100901)
                    ·
                      refine ⟨2183486624130180492581419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11645261995360962627100901 2183486624130180492581419)
                      ·
                        rfl

theorem cell23_4252325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4252325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252325 prefixEnd_4252325 := by exact prefixLift 4252325
  have htrace : WordTrace (prefixWord ++ tailWord_4252325) baseStart_4252325 baseEnd_4252325 := by
    simpa [prefixWord, tailWord_4252325, baseEnd_4252325] using wordTrace_append hprefix tailTrace_4252325
  have hstable : (prefixWord ++ tailWord_4252325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252325).length < 2 ^ (prefixWord ++ tailWord_4252325).sum := by decide
  have hdescent : baseEnd_4252325 < baseStart_4252325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252352 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_4252352 : Nat := 118140960795 + 4252352 * 2 ^ 59
def prefixEnd_4252352 : Nat := 4983230072969 + 3 ^ 40 * 4252352 * 2
def baseEnd_4252352 : Nat := 727833496035950628981265

theorem tailTrace_4252352 : CollatzResearch.WordTrace tailWord_4252352 prefixEnd_4252352 727833496035950628981265 := by
  unfold tailWord_4252352
  simp only [CollatzResearch.WordTrace]
  refine ⟨77548009545231211373739655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103397346060308281831652873 77548009545231211373739655)
  ·
    refine ⟨116322014317846817060609483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77548009545231211373739655 116322014317846817060609483)
    ·
      refine ⟨174483021476770225590914225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116322014317846817060609483 174483021476770225590914225)
      ·
        refine ⟨130862266107577669193185669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174483021476770225590914225 130862266107577669193185669)
        ·
          refine ⟨24536674895170812973722313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130862266107577669193185669 24536674895170812973722313)
          ·
            refine ⟨18402506171378109730291735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24536674895170812973722313 18402506171378109730291735)
            ·
              refine ⟨27603759257067164595437603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18402506171378109730291735 27603759257067164595437603)
              ·
                refine ⟨41405638885600746893156405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27603759257067164595437603 41405638885600746893156405)
                ·
                  refine ⟨3881778645525070021233413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41405638885600746893156405 3881778645525070021233413)
                  ·
                    refine ⟨727833496035950628981265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881778645525070021233413 727833496035950628981265)
                    ·
                      rfl

theorem cell23_4252352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_4252352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252352 prefixEnd_4252352 := by exact prefixLift 4252352
  have htrace : WordTrace (prefixWord ++ tailWord_4252352) baseStart_4252352 baseEnd_4252352 := by
    simpa [prefixWord, tailWord_4252352, baseEnd_4252352] using wordTrace_append hprefix tailTrace_4252352
  have hstable : (prefixWord ++ tailWord_4252352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252352).length < 2 ^ (prefixWord ++ tailWord_4252352).sum := by decide
  have hdescent : baseEnd_4252352 < baseStart_4252352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252399 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 6]
def baseStart_4252399 : Nat := 118140960795 + 4252399 * 2 ^ 59
def prefixEnd_4252399 : Nat := 4983230072969 + 3 ^ 40 * 4252399 * 2
def baseEnd_4252399 : Nat := 242613846855401467006231

theorem tailTrace_4252399 : CollatzResearch.WordTrace tailWord_4252399 prefixEnd_4252399 242613846855401467006231 := by
  unfold tailWord_4252399
  simp only [CollatzResearch.WordTrace]
  refine ⟨155097733321292149774440251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103398488880861433182960167 155097733321292149774440251)
  ·
    refine ⟨232646599981938224661660377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155097733321292149774440251 232646599981938224661660377)
    ·
      refine ⟨174484949986453668496245283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232646599981938224661660377 174484949986453668496245283)
      ·
        refine ⟨261727424979680502744367925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174484949986453668496245283 261727424979680502744367925)
        ·
          refine ⟨24536946091845047132284493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 261727424979680502744367925 24536946091845047132284493)
          ·
            refine ⟨9201354784441892674606685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24536946091845047132284493 9201354784441892674606685)
            ·
              refine ⟨3450508044165709752977507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9201354784441892674606685 3450508044165709752977507)
              ·
                refine ⟨5175762066248564629466261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450508044165709752977507 5175762066248564629466261)
                ·
                  refine ⟨242613846855401467006231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5175762066248564629466261 242613846855401467006231)
                  ·
                    rfl

theorem cell23_4252399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 6].length) (baseStart_4252399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252399 prefixEnd_4252399 := by exact prefixLift 4252399
  have htrace : WordTrace (prefixWord ++ tailWord_4252399) baseStart_4252399 baseEnd_4252399 := by
    simpa [prefixWord, tailWord_4252399, baseEnd_4252399] using wordTrace_append hprefix tailTrace_4252399
  have hstable : (prefixWord ++ tailWord_4252399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252399).length < 2 ^ (prefixWord ++ tailWord_4252399).sum := by decide
  have hdescent : baseEnd_4252399 < baseStart_4252399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252419 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 2, 3, 2]
def baseStart_4252419 : Nat := 118140960795 + 4252419 * 2 ^ 59
def prefixEnd_4252419 : Nat := 4983230072969 + 3 ^ 40 * 4252419 * 2
def baseEnd_4252419 : Nat := 2183534891311703124805987

theorem tailTrace_4252419 : CollatzResearch.WordTrace tailWord_4252419 prefixEnd_4252419 2183534891311703124805987 := by
  unfold tailWord_4252419
  simp only [CollatzResearch.WordTrace]
  refine ⟨155098462781219693190168311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103398975187479795460112207 155098462781219693190168311)
  ·
    refine ⟨232647694171829539785252467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155098462781219693190168311 232647694171829539785252467)
    ·
      refine ⟨348971541257744309677878701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232647694171829539785252467 348971541257744309677878701)
      ·
        refine ⟨130864327971654116129204513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348971541257744309677878701 130864327971654116129204513)
        ·
          refine ⟨98148245978740587096903385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130864327971654116129204513 98148245978740587096903385)
          ·
            refine ⟨73611184484055440322677539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98148245978740587096903385 73611184484055440322677539)
            ·
              refine ⟨110416776726083160484016309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73611184484055440322677539 110416776726083160484016309)
              ·
                refine ⟨10351572818070296295376529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110416776726083160484016309 10351572818070296295376529)
                ·
                  refine ⟨7763679613552722221532397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10351572818070296295376529 7763679613552722221532397)
                  ·
                    refine ⟨2911379855082270833074649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7763679613552722221532397 2911379855082270833074649)
                    ·
                      refine ⟨2183534891311703124805987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911379855082270833074649 2183534891311703124805987)
                      ·
                        rfl

theorem cell23_4252419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_4252419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252419 prefixEnd_4252419 := by exact prefixLift 4252419
  have htrace : WordTrace (prefixWord ++ tailWord_4252419) baseStart_4252419 baseEnd_4252419 := by
    simpa [prefixWord, tailWord_4252419, baseEnd_4252419] using wordTrace_append hprefix tailTrace_4252419
  have hstable : (prefixWord ++ tailWord_4252419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252419).length < 2 ^ (prefixWord ++ tailWord_4252419).sum := by decide
  have hdescent : baseEnd_4252419 < baseStart_4252419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252466 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_4252466 : Nat := 118140960795 + 4252466 * 2 ^ 59
def prefixEnd_4252466 : Nat := 4983230072969 + 3 ^ 40 * 4252466 * 2
def baseEnd_4252466 : Nat := 2183559024902464440918271

theorem tailTrace_4252466 : CollatzResearch.WordTrace tailWord_4252466 prefixEnd_4252466 2183559024902464440918271 := by
  unfold tailWord_4252466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38775044253012355054282313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103400118008032946811419501 38775044253012355054282313)
  ·
    refine ⟨29081283189759266290711735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38775044253012355054282313 29081283189759266290711735)
    ·
      refine ⟨43621924784638899436067603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29081283189759266290711735 43621924784638899436067603)
      ·
        refine ⟨65432887176958349154101405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43621924784638899436067603 65432887176958349154101405)
        ·
          refine ⟨24537332691359380932788027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65432887176958349154101405 24537332691359380932788027)
          ·
            refine ⟨36805999037039071399182041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24537332691359380932788027 36805999037039071399182041)
            ·
              refine ⟨27604499277779303549386531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36805999037039071399182041 27604499277779303549386531)
              ·
                refine ⟨41406748916668955324079797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27604499277779303549386531 41406748916668955324079797)
                ·
                  refine ⟨3881882710937714561632481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41406748916668955324079797 3881882710937714561632481)
                  ·
                    refine ⟨2911412033203285921224361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3881882710937714561632481 2911412033203285921224361)
                    ·
                      refine ⟨2183559024902464440918271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911412033203285921224361 2183559024902464440918271)
                      ·
                        rfl

theorem cell23_4252466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_4252466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252466 prefixEnd_4252466 := by exact prefixLift 4252466
  have htrace : WordTrace (prefixWord ++ tailWord_4252466) baseStart_4252466 baseEnd_4252466 := by
    simpa [prefixWord, tailWord_4252466, baseEnd_4252466] using wordTrace_append hprefix tailTrace_4252466
  have hstable : (prefixWord ++ tailWord_4252466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252466).length < 2 ^ (prefixWord ++ tailWord_4252466).sum := by decide
  have hdescent : baseEnd_4252466 < baseStart_4252466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252470 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4252470 : Nat := 118140960795 + 4252470 * 2 ^ 59
def prefixEnd_4252470 : Nat := 4983230072969 + 3 ^ 40 * 4252470 * 2
def baseEnd_4252470 : Nat := 2183561078825082425268253

theorem tailTrace_4252470 : CollatzResearch.WordTrace tailWord_4252470 prefixEnd_4252470 2183561078825082425268253 := by
  unfold tailWord_4252470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693770181502183056267179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103400215269356619266849909 9693770181502183056267179)
  ·
    refine ⟨14540655272253274584400769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693770181502183056267179 14540655272253274584400769)
    ·
      refine ⟨10905491454189955938300577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14540655272253274584400769 10905491454189955938300577)
      ·
        refine ⟨8179118590642466953725433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10905491454189955938300577 8179118590642466953725433)
        ·
          refine ⟨6134338942981850215294075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8179118590642466953725433 6134338942981850215294075)
          ·
            refine ⟨9201508414472775322941113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134338942981850215294075 9201508414472775322941113)
            ·
              refine ⟨6901131310854581492205835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9201508414472775322941113 6901131310854581492205835)
              ·
                refine ⟨10351696966281872238308753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901131310854581492205835 10351696966281872238308753)
                ·
                  refine ⟨7763772724711404178731565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10351696966281872238308753 7763772724711404178731565)
                  ·
                    refine ⟨2911414771766776567024337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7763772724711404178731565 2911414771766776567024337)
                    ·
                      refine ⟨2183561078825082425268253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911414771766776567024337 2183561078825082425268253)
                      ·
                        rfl

theorem cell23_4252470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4252470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252470 prefixEnd_4252470 := by exact prefixLift 4252470
  have htrace : WordTrace (prefixWord ++ tailWord_4252470) baseStart_4252470 baseEnd_4252470 := by
    simpa [prefixWord, tailWord_4252470, baseEnd_4252470] using wordTrace_append hprefix tailTrace_4252470
  have hstable : (prefixWord ++ tailWord_4252470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252470).length < 2 ^ (prefixWord ++ tailWord_4252470).sum := by decide
  have hdescent : baseEnd_4252470 < baseStart_4252470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252479 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_4252479 : Nat := 118140960795 + 4252479 * 2 ^ 59
def prefixEnd_4252479 : Nat := 4983230072969 + 3 ^ 40 * 4252479 * 2
def baseEnd_4252479 : Nat := 2183565700150972890055711

theorem tailTrace_4252479 : CollatzResearch.WordTrace tailWord_4252479 prefixEnd_4252479 2183565700150972890055711 := by
  unfold tailWord_4252479
  simp only [CollatzResearch.WordTrace]
  refine ⟨155100651161002323437352491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103400434107334882291568327 155100651161002323437352491)
  ·
    refine ⟨232650976741503485156028737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155100651161002323437352491 232650976741503485156028737)
    ·
      refine ⟨174488232556127613867021553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232650976741503485156028737 174488232556127613867021553)
      ·
        refine ⟨130866174417095710400266165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174488232556127613867021553 130866174417095710400266165)
        ·
          refine ⟨12268703851602722850024953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130866174417095710400266165 12268703851602722850024953)
          ·
            refine ⟨9201527888702042137518715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12268703851602722850024953 9201527888702042137518715)
            ·
              refine ⟨13802291833053063206278073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9201527888702042137518715 13802291833053063206278073)
              ·
                refine ⟨10351718874789797404708555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13802291833053063206278073 10351718874789797404708555)
                ·
                  refine ⟨15527578312184696107062833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10351718874789797404708555 15527578312184696107062833)
                  ·
                    refine ⟨11645683734138522080297125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15527578312184696107062833 11645683734138522080297125)
                    ·
                      refine ⟨2183565700150972890055711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11645683734138522080297125 2183565700150972890055711)
                      ·
                        rfl

theorem cell23_4252479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_4252479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252479 prefixEnd_4252479 := by exact prefixLift 4252479
  have htrace : WordTrace (prefixWord ++ tailWord_4252479) baseStart_4252479 baseEnd_4252479 := by
    simpa [prefixWord, tailWord_4252479, baseEnd_4252479] using wordTrace_append hprefix tailTrace_4252479
  have hstable : (prefixWord ++ tailWord_4252479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252479).length < 2 ^ (prefixWord ++ tailWord_4252479).sum := by decide
  have hdescent : baseEnd_4252479 < baseStart_4252479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252483 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 1, 2, 2]
def baseStart_4252483 : Nat := 118140960795 + 4252483 * 2 ^ 59
def prefixEnd_4252483 : Nat := 4983230072969 + 3 ^ 40 * 4252483 * 2
def baseEnd_4252483 : Nat := 2183567754073590874405693

theorem tailTrace_4252483 : CollatzResearch.WordTrace tailWord_4252483 prefixEnd_4252483 2183567754073590874405693 := by
  unfold tailWord_4252483
  simp only [CollatzResearch.WordTrace]
  refine ⟨155100797052987832120498103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103400531368658554746998735 155100797052987832120498103)
  ·
    refine ⟨232651195579481748180747155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155100797052987832120498103 232651195579481748180747155)
    ·
      refine ⟨348976793369222622271120733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232651195579481748180747155 348976793369222622271120733)
      ·
        refine ⟨130866297513458483351670275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348976793369222622271120733 130866297513458483351670275)
        ·
          refine ⟨196299446270187725027505413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130866297513458483351670275 196299446270187725027505413)
          ·
            refine ⟨36806146175660198442657265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196299446270187725027505413 36806146175660198442657265)
            ·
              refine ⟨27604609631745148831992949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36806146175660198442657265 27604609631745148831992949)
              ·
                refine ⟨2587932152976107702999339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27604609631745148831992949 2587932152976107702999339)
                ·
                  refine ⟨3881898229464161554499009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587932152976107702999339 3881898229464161554499009)
                  ·
                    refine ⟨2911423672098121165874257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3881898229464161554499009 2911423672098121165874257)
                    ·
                      refine ⟨2183567754073590874405693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911423672098121165874257 2183567754073590874405693)
                      ·
                        rfl

theorem cell23_4252483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_4252483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252483 prefixEnd_4252483 := by exact prefixLift 4252483
  have htrace : WordTrace (prefixWord ++ tailWord_4252483) baseStart_4252483 baseEnd_4252483 := by
    simpa [prefixWord, tailWord_4252483, baseEnd_4252483] using wordTrace_append hprefix tailTrace_4252483
  have hstable : (prefixWord ++ tailWord_4252483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252483).length < 2 ^ (prefixWord ++ tailWord_4252483).sum := by decide
  have hdescent : baseEnd_4252483 < baseStart_4252483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252499 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 3]
def baseStart_4252499 : Nat := 118140960795 + 4252499 * 2 ^ 59
def prefixEnd_4252499 : Nat := 4983230072969 + 3 ^ 40 * 4252499 * 2
def baseEnd_4252499 : Nat := 2183575969764062811805619

theorem tailTrace_4252499 : CollatzResearch.WordTrace tailWord_4252499 prefixEnd_4252499 2183575969764062811805619 := by
  unfold tailWord_4252499
  simp only [CollatzResearch.WordTrace]
  refine ⟨155101380620929866853080551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103400920413953244568720367 155101380620929866853080551)
  ·
    refine ⟨232652070931394800279620827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155101380620929866853080551 232652070931394800279620827)
    ·
      refine ⟨348978106397092200419431241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232652070931394800279620827 348978106397092200419431241)
      ·
        refine ⟨261733579797819150314573431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348978106397092200419431241 261733579797819150314573431)
        ·
          refine ⟨392600369696728725471860147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261733579797819150314573431 392600369696728725471860147)
          ·
            refine ⟨588900554545093088207790221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392600369696728725471860147 588900554545093088207790221)
            ·
              refine ⟨220837707954409908077921333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588900554545093088207790221 220837707954409908077921333)
              ·
                refine ⟨20703535120725928882305125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220837707954409908077921333 20703535120725928882305125)
                ·
                  refine ⟨3881912835136111665432211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20703535120725928882305125 3881912835136111665432211)
                  ·
                    refine ⟨5822869252704167498148317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881912835136111665432211 5822869252704167498148317)
                    ·
                      refine ⟨2183575969764062811805619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5822869252704167498148317 2183575969764062811805619)
                      ·
                        rfl

theorem cell23_4252499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_4252499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252499 prefixEnd_4252499 := by exact prefixLift 4252499
  have htrace : WordTrace (prefixWord ++ tailWord_4252499) baseStart_4252499 baseEnd_4252499 := by
    simpa [prefixWord, tailWord_4252499, baseEnd_4252499] using wordTrace_append hprefix tailTrace_4252499
  have hstable : (prefixWord ++ tailWord_4252499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252499).length < 2 ^ (prefixWord ++ tailWord_4252499).sum := by decide
  have hdescent : baseEnd_4252499 < baseStart_4252499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252516 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_4252516 : Nat := 118140960795 + 4252516 * 2 ^ 59
def prefixEnd_4252516 : Nat := 4983230072969 + 3 ^ 40 * 4252516 * 2
def baseEnd_4252516 : Nat := 2183584698935189245293041

theorem tailTrace_4252516 : CollatzResearch.WordTrace tailWord_4252516 prefixEnd_4252516 2183584698935189245293041 := by
  unfold tailWord_4252516
  simp only [CollatzResearch.WordTrace]
  refine ⟨77551000330934139378224701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103401333774578852504299601 77551000330934139378224701)
  ·
    refine ⟨29081625124100302266834263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77551000330934139378224701 29081625124100302266834263)
    ·
      refine ⟨43622437686150453400251395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29081625124100302266834263 43622437686150453400251395)
      ·
        refine ⟨65433656529225680100377093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43622437686150453400251395 65433656529225680100377093)
        ·
          refine ⟨12268810599229815018820705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65433656529225680100377093 12268810599229815018820705)
          ·
            refine ⟨9201607949422361264115529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12268810599229815018820705 9201607949422361264115529)
            ·
              refine ⟨6901205962066770948086647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9201607949422361264115529 6901205962066770948086647)
              ·
                refine ⟨10351808943100156422129971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901205962066770948086647 10351808943100156422129971)
                ·
                  refine ⟨15527713414650234633194957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10351808943100156422129971 15527713414650234633194957)
                  ·
                    refine ⟨5822892530493837987448109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15527713414650234633194957 5822892530493837987448109)
                    ·
                      refine ⟨2183584698935189245293041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5822892530493837987448109 2183584698935189245293041)
                      ·
                        rfl

theorem cell23_4252516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_4252516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252516 prefixEnd_4252516 := by exact prefixLift 4252516
  have htrace : WordTrace (prefixWord ++ tailWord_4252516) baseStart_4252516 baseEnd_4252516 := by
    simpa [prefixWord, tailWord_4252516, baseEnd_4252516] using wordTrace_append hprefix tailTrace_4252516
  have hstable : (prefixWord ++ tailWord_4252516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252516).length < 2 ^ (prefixWord ++ tailWord_4252516).sum := by decide
  have hdescent : baseEnd_4252516 < baseStart_4252516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252543 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 1, 3, 2]
def baseStart_4252543 : Nat := 118140960795 + 4252543 * 2 ^ 59
def prefixEnd_4252543 : Nat := 4983230072969 + 3 ^ 40 * 4252543 * 2
def baseEnd_4252543 : Nat := 2183598562912860639655417

theorem tailTrace_4252543 : CollatzResearch.WordTrace tailWord_4252543 prefixEnd_4252543 2183598562912860639655417 := by
  unfold tailWord_4252543
  simp only [CollatzResearch.WordTrace]
  refine ⟨155102985432770462367682283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103401990288513641578454855 155102985432770462367682283)
  ·
    refine ⟨232654478149155693551523425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155102985432770462367682283 232654478149155693551523425)
    ·
      refine ⟨174490858611866770163642569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232654478149155693551523425 174490858611866770163642569)
      ·
        refine ⟨130868143958900077622731927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174490858611866770163642569 130868143958900077622731927)
        ·
          refine ⟨196302215938350116434097891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130868143958900077622731927 196302215938350116434097891)
          ·
            refine ⟨294453323907525174651146837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196302215938350116434097891 294453323907525174651146837)
            ·
              refine ⟨3450624889541310640443127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 294453323907525174651146837 3450624889541310640443127)
              ·
                refine ⟨5175937334311965960664691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450624889541310640443127 5175937334311965960664691)
                ·
                  refine ⟨7763906001467948940997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5175937334311965960664691 7763906001467948940997037)
                  ·
                    refine ⟨2911464750550480852873889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7763906001467948940997037 2911464750550480852873889)
                    ·
                      refine ⟨2183598562912860639655417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911464750550480852873889 2183598562912860639655417)
                      ·
                        rfl

theorem cell23_4252543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_4252543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252543 prefixEnd_4252543 := by exact prefixLift 4252543
  have htrace : WordTrace (prefixWord ++ tailWord_4252543) baseStart_4252543 baseEnd_4252543 := by
    simpa [prefixWord, tailWord_4252543, baseEnd_4252543] using wordTrace_append hprefix tailTrace_4252543
  have hstable : (prefixWord ++ tailWord_4252543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252543).length < 2 ^ (prefixWord ++ tailWord_4252543).sum := by decide
  have hdescent : baseEnd_4252543 < baseStart_4252543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252619 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_4252619 : Nat := 118140960795 + 4252619 * 2 ^ 59
def prefixEnd_4252619 : Nat := 4983230072969 + 3 ^ 40 * 4252619 * 2
def baseEnd_4252619 : Nat := 2183637587442602342305067

theorem tailTrace_4252619 : CollatzResearch.WordTrace tailWord_4252619 prefixEnd_4252619 2183637587442602342305067 := by
  unfold tailWord_4252619
  simp only [CollatzResearch.WordTrace]
  refine ⟨155105757380495127347448911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103403838253663418231632607 155105757380495127347448911)
  ·
    refine ⟨232658636070742691021173367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155105757380495127347448911 232658636070742691021173367)
    ·
      refine ⟨348987954106114036531760051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232658636070742691021173367 348987954106114036531760051)
      ·
        refine ⟨523481931159171054797640077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348987954106114036531760051 523481931159171054797640077)
        ·
          refine ⟨196305724184689145549115029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523481931159171054797640077 196305724184689145549115029)
          ·
            refine ⟨9201830821157303697614767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196305724184689145549115029 9201830821157303697614767)
            ·
              refine ⟨13802746231735955546422151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9201830821157303697614767 13802746231735955546422151)
              ·
                refine ⟨20704119347603933319633227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13802746231735955546422151 20704119347603933319633227)
                ·
                  refine ⟨31056179021405899979449841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20704119347603933319633227 31056179021405899979449841)
                  ·
                    refine ⟨23292134266054424984587381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31056179021405899979449841 23292134266054424984587381)
                    ·
                      refine ⟨2183637587442602342305067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23292134266054424984587381 2183637587442602342305067)
                      ·
                        rfl

theorem cell23_4252619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_4252619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252619 prefixEnd_4252619 := by exact prefixLift 4252619
  have htrace : WordTrace (prefixWord ++ tailWord_4252619) baseStart_4252619 baseEnd_4252619 := by
    simpa [prefixWord, tailWord_4252619, baseEnd_4252619] using wordTrace_append hprefix tailTrace_4252619
  have hstable : (prefixWord ++ tailWord_4252619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252619).length < 2 ^ (prefixWord ++ tailWord_4252619).sum := by decide
  have hdescent : baseEnd_4252619 < baseStart_4252619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252686 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_4252686 : Nat := 118140960795 + 4252686 * 2 ^ 59
def prefixEnd_4252686 : Nat := 4983230072969 + 3 ^ 40 * 4252686 * 2
def baseEnd_4252686 : Nat := 242630221182939286685251

theorem tailTrace_4252686 : CollatzResearch.WordTrace tailWord_4252686 prefixEnd_4252686 242630221182939286685251 := by
  unfold tailWord_4252686
  simp only [CollatzResearch.WordTrace]
  refine ⟨19388525133906549723767239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103405467380834931860091941 19388525133906549723767239)
  ·
    refine ⟨29082787700859824585650859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19388525133906549723767239 29082787700859824585650859)
    ·
      refine ⟨43624181551289736878476289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29082787700859824585650859 43624181551289736878476289)
      ·
        refine ⟨32718136163467302658857217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43624181551289736878476289 32718136163467302658857217)
        ·
          refine ⟨24538602122600476994142913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32718136163467302658857217 24538602122600476994142913)
          ·
            refine ⟨18403951591950357745607185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24538602122600476994142913 18403951591950357745607185)
            ·
              refine ⟨13802963693962768309205389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18403951591950357745607185 13802963693962768309205389)
              ·
                refine ⟨5176111385236038115952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13802963693962768309205389 5176111385236038115952021)
                ·
                  refine ⟨242630221182939286685251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5176111385236038115952021 242630221182939286685251)
                  ·
                    rfl

theorem cell23_4252686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_4252686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252686 prefixEnd_4252686 := by exact prefixLift 4252686
  have htrace : WordTrace (prefixWord ++ tailWord_4252686) baseStart_4252686 baseEnd_4252686 := by
    simpa [prefixWord, tailWord_4252686, baseEnd_4252686] using wordTrace_append hprefix tailTrace_4252686
  have hstable : (prefixWord ++ tailWord_4252686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252686).length < 2 ^ (prefixWord ++ tailWord_4252686).sum := by decide
  have hdescent : baseEnd_4252686 < baseStart_4252686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252700 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4252700 : Nat := 118140960795 + 4252700 * 2 ^ 59
def prefixEnd_4252700 : Nat := 4983230072969 + 3 ^ 40 * 4252700 * 2
def baseEnd_4252700 : Nat := 2183679179375616525392195

theorem tailTrace_4252700 : CollatzResearch.WordTrace tailWord_4252700 prefixEnd_4252700 2183679179375616525392195 := by
  unfold tailWord_4252700
  simp only [CollatzResearch.WordTrace]
  refine ⟨77554355846600839090573777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103405807795467785454098369 77554355846600839090573777)
  ·
    refine ⟨58165766884950629317930333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77554355846600839090573777 58165766884950629317930333)
    ·
      refine ⟨21812162581856485994223875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58165766884950629317930333 21812162581856485994223875)
      ·
        refine ⟨32718243872784728991335813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21812162581856485994223875 32718243872784728991335813)
        ·
          refine ⟨6134670726147136685875465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32718243872784728991335813 6134670726147136685875465)
          ·
            refine ⟨4601003044610352514406599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6134670726147136685875465 4601003044610352514406599)
            ·
              refine ⟨6901504566915528771609899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601003044610352514406599 6901504566915528771609899)
              ·
                refine ⟨10352256850373293157414849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901504566915528771609899 10352256850373293157414849)
                ·
                  refine ⟨7764192637779969868061137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10352256850373293157414849 7764192637779969868061137)
                  ·
                    refine ⟨5823144478334977401045853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7764192637779969868061137 5823144478334977401045853)
                    ·
                      refine ⟨2183679179375616525392195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823144478334977401045853 2183679179375616525392195)
                      ·
                        rfl

theorem cell23_4252700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4252700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252700 prefixEnd_4252700 := by exact prefixLift 4252700
  have htrace : WordTrace (prefixWord ++ tailWord_4252700) baseStart_4252700 baseEnd_4252700 := by
    simpa [prefixWord, tailWord_4252700, baseEnd_4252700] using wordTrace_append hprefix tailTrace_4252700
  have hstable : (prefixWord ++ tailWord_4252700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252700).length < 2 ^ (prefixWord ++ tailWord_4252700).sum := by decide
  have hdescent : baseEnd_4252700 < baseStart_4252700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252716 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_4252716 : Nat := 118140960795 + 4252716 * 2 ^ 59
def prefixEnd_4252716 : Nat := 4983230072969 + 3 ^ 40 * 4252716 * 2
def baseEnd_4252716 : Nat := 727895798355362820930707

theorem tailTrace_4252716 : CollatzResearch.WordTrace tailWord_4252716 prefixEnd_4252716 727895798355362820930707 := by
  unfold tailWord_4252716
  simp only [CollatzResearch.WordTrace]
  refine ⟨77554647630571856456865001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103406196840762475275820001 77554647630571856456865001)
  ·
    refine ⟨58165985722928892342648751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77554647630571856456865001 58165985722928892342648751)
    ·
      refine ⟨87248978584393338513973127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58165985722928892342648751 87248978584393338513973127)
      ·
        refine ⟨130873467876590007770959691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87248978584393338513973127 130873467876590007770959691)
        ·
          refine ⟨196310201814885011656439537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130873467876590007770959691 196310201814885011656439537)
          ·
            refine ⟨147232651361163758742329653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196310201814885011656439537 147232651361163758742329653)
            ·
              refine ⟨13803061065109102382093405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147232651361163758742329653 13803061065109102382093405)
              ·
                refine ⟨5176147899415913393285027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13803061065109102382093405 5176147899415913393285027)
                ·
                  refine ⟨7764221849123870089927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176147899415913393285027 7764221849123870089927541)
                  ·
                    refine ⟨727895798355362820930707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7764221849123870089927541 727895798355362820930707)
                    ·
                      rfl

theorem cell23_4252716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_4252716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252716 prefixEnd_4252716 := by exact prefixLift 4252716
  have htrace : WordTrace (prefixWord ++ tailWord_4252716) baseStart_4252716 baseEnd_4252716 := by
    simpa [prefixWord, tailWord_4252716, baseEnd_4252716] using wordTrace_append hprefix tailTrace_4252716
  have hstable : (prefixWord ++ tailWord_4252716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252716).length < 2 ^ (prefixWord ++ tailWord_4252716).sum := by decide
  have hdescent : baseEnd_4252716 < baseStart_4252716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252730 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_4252730 : Nat := 118140960795 + 4252730 * 2 ^ 59
def prefixEnd_4252730 : Nat := 4983230072969 + 3 ^ 40 * 4252730 * 2
def baseEnd_4252730 : Nat := 2183694583795251408017057

theorem tailTrace_4252730 : CollatzResearch.WordTrace tailWord_4252730 prefixEnd_4252730 2183694583795251408017057 := by
  unfold tailWord_4252730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38777451470773248326184911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103406537255395328869826429 38777451470773248326184911)
  ·
    refine ⟨58166177206159872489277367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38777451470773248326184911 58166177206159872489277367)
    ·
      refine ⟨87249265809239808733916051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58166177206159872489277367 87249265809239808733916051)
      ·
        refine ⟨130873898713859713100874077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87249265809239808733916051 130873898713859713100874077)
        ·
          refine ⟨49077712017697392412827779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130873898713859713100874077 49077712017697392412827779)
          ·
            refine ⟨73616568026546088619241669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49077712017697392412827779 73616568026546088619241669)
            ·
              refine ⟨13803106504977391616107813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73616568026546088619241669 13803106504977391616107813)
              ·
                refine ⟨2588082469683260928020215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13803106504977391616107813 2588082469683260928020215)
                ·
                  refine ⟨3882123704524891392030323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588082469683260928020215 3882123704524891392030323)
                  ·
                    refine ⟨5823185556787337088045485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3882123704524891392030323 5823185556787337088045485)
                    ·
                      refine ⟨2183694583795251408017057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823185556787337088045485 2183694583795251408017057)
                      ·
                        rfl

theorem cell23_4252730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_4252730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252730 prefixEnd_4252730 := by exact prefixLift 4252730
  have htrace : WordTrace (prefixWord ++ tailWord_4252730) baseStart_4252730 baseEnd_4252730 := by
    simpa [prefixWord, tailWord_4252730, baseEnd_4252730] using wordTrace_append hprefix tailTrace_4252730
  have hstable : (prefixWord ++ tailWord_4252730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252730).length < 2 ^ (prefixWord ++ tailWord_4252730).sum := by decide
  have hdescent : baseEnd_4252730 < baseStart_4252730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252746 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_4252746 : Nat := 118140960795 + 4252746 * 2 ^ 59
def prefixEnd_4252746 : Nat := 4983230072969 + 3 ^ 40 * 4252746 * 2
def baseEnd_4252746 : Nat := 727900933161907781805661

theorem tailTrace_4252746 : CollatzResearch.WordTrace tailWord_4252746 prefixEnd_4252746 727900933161907781805661 := by
  unfold tailWord_4252746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38777597362758757009330523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103406926300690018691548061 38777597362758757009330523)
  ·
    refine ⟨58166396044138135513995785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38777597362758757009330523 58166396044138135513995785)
    ·
      refine ⟨43624797033103601635496839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58166396044138135513995785 43624797033103601635496839)
      ·
        refine ⟨65437195549655402453245259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43624797033103601635496839 65437195549655402453245259)
        ·
          refine ⟨98155793324483103679867889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65437195549655402453245259 98155793324483103679867889)
          ·
            refine ⟨73616844993362327759900917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98155793324483103679867889 73616844993362327759900917)
            ·
              refine ⟨6901579218127718227490711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73616844993362327759900917 6901579218127718227490711)
              ·
                refine ⟨10352368827191577341236067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901579218127718227490711 10352368827191577341236067)
                ·
                  refine ⟨15528553240787366011854101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10352368827191577341236067 15528553240787366011854101)
                  ·
                    refine ⟨727900933161907781805661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15528553240787366011854101 727900933161907781805661)
                    ·
                      rfl

theorem cell23_4252746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_4252746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252746 prefixEnd_4252746 := by exact prefixLift 4252746
  have htrace : WordTrace (prefixWord ++ tailWord_4252746) baseStart_4252746 baseEnd_4252746 := by
    simpa [prefixWord, tailWord_4252746, baseEnd_4252746] using wordTrace_append hprefix tailTrace_4252746
  have hstable : (prefixWord ++ tailWord_4252746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252746).length < 2 ^ (prefixWord ++ tailWord_4252746).sum := by decide
  have hdescent : baseEnd_4252746 < baseStart_4252746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252770 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4252770 : Nat := 118140960795 + 4252770 * 2 ^ 59
def prefixEnd_4252770 : Nat := 4983230072969 + 3 ^ 40 * 4252770 * 2
def baseEnd_4252770 : Nat := 2183715123021431251516873

theorem tailTrace_4252770 : CollatzResearch.WordTrace tailWord_4252770 prefixEnd_4252770 2183715123021431251516873 := by
  unfold tailWord_4252770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38777816200737020034048941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103407509868632053424130509 38777816200737020034048941)
  ·
    refine ⟨14541681075276382512768353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38777816200737020034048941 14541681075276382512768353)
    ·
      refine ⟨10906260806457286884576265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14541681075276382512768353 10906260806457286884576265)
      ·
        refine ⟨8179695604842965163432199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10906260806457286884576265 8179695604842965163432199)
        ·
          refine ⟨12269543407264447745148299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8179695604842965163432199 12269543407264447745148299)
          ·
            refine ⟨18404315110896671617722449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12269543407264447745148299 18404315110896671617722449)
            ·
              refine ⟨13803236333172503713291837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18404315110896671617722449 13803236333172503713291837)
              ·
                refine ⟨5176213624939688892484439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13803236333172503713291837 5176213624939688892484439)
                ·
                  refine ⟨7764320437409533338726659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176213624939688892484439 7764320437409533338726659)
                  ·
                    refine ⟨11646480656114300008089989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7764320437409533338726659 11646480656114300008089989)
                    ·
                      refine ⟨2183715123021431251516873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11646480656114300008089989 2183715123021431251516873)
                      ·
                        rfl

theorem cell23_4252770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4252770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252770 prefixEnd_4252770 := by exact prefixLift 4252770
  have htrace : WordTrace (prefixWord ++ tailWord_4252770) baseStart_4252770 baseEnd_4252770 := by
    simpa [prefixWord, tailWord_4252770, baseEnd_4252770] using wordTrace_append hprefix tailTrace_4252770
  have hstable : (prefixWord ++ tailWord_4252770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252770).length < 2 ^ (prefixWord ++ tailWord_4252770).sum := by decide
  have hdescent : baseEnd_4252770 < baseStart_4252770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252773 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4252773 : Nat := 118140960795 + 4252773 * 2 ^ 59
def prefixEnd_4252773 : Nat := 4983230072969 + 3 ^ 40 * 4252773 * 2
def baseEnd_4252773 : Nat := 2183716663463394739779359

theorem tailTrace_4252773 : CollatzResearch.WordTrace tailWord_4252773 prefixEnd_4252773 2183716663463394739779359 := by
  unfold tailWord_4252773
  simp only [CollatzResearch.WordTrace]
  refine ⟨155111374221937211648554973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103407582814624807765703315 155111374221937211648554973)
  ·
    refine ⟨58166765333226454368208115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155111374221937211648554973 58166765333226454368208115)
    ·
      refine ⟨87250147999839681552312173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58166765333226454368208115 87250147999839681552312173)
      ·
        refine ⟨32718805499939880582117065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87250147999839681552312173 32718805499939880582117065)
        ·
          refine ⟨24539104124954910436587799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32718805499939880582117065 24539104124954910436587799)
          ·
            refine ⟨36808656187432365654881699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24539104124954910436587799 36808656187432365654881699)
            ·
              refine ⟨55212984281148548482322549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36808656187432365654881699 55212984281148548482322549)
              ·
                refine ⟨5176217276357676420217739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55212984281148548482322549 5176217276357676420217739)
                ·
                  refine ⟨7764325914536514630326609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176217276357676420217739 7764325914536514630326609)
                  ·
                    refine ⟨5823244435902385972744957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7764325914536514630326609 5823244435902385972744957)
                    ·
                      refine ⟨2183716663463394739779359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823244435902385972744957 2183716663463394739779359)
                      ·
                        rfl

theorem cell23_4252773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4252773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252773 prefixEnd_4252773 := by exact prefixLift 4252773
  have htrace : WordTrace (prefixWord ++ tailWord_4252773) baseStart_4252773 baseEnd_4252773 := by
    simpa [prefixWord, tailWord_4252773, baseEnd_4252773] using wordTrace_append hprefix tailTrace_4252773
  have hstable : (prefixWord ++ tailWord_4252773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252773).length < 2 ^ (prefixWord ++ tailWord_4252773).sum := by decide
  have hdescent : baseEnd_4252773 < baseStart_4252773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252854 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4252854 : Nat := 118140960795 + 4252854 * 2 ^ 59
def prefixEnd_4252854 : Nat := 4983230072969 + 3 ^ 40 * 4252854 * 2
def baseEnd_4252854 : Nat := 2183758255396408922866487

theorem tailTrace_4252854 : CollatzResearch.WordTrace tailWord_4252854 prefixEnd_4252854 2183758255396408922866487 := by
  unfold tailWord_4252854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694645533415235155140851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103409552356429174988169077 9694645533415235155140851)
  ·
    refine ⟨14541968300122852732711277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694645533415235155140851 14541968300122852732711277)
    ·
      refine ⟨5453238112546069774766729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14541968300122852732711277 5453238112546069774766729)
      ·
        refine ⟨4089928584409552331075047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5453238112546069774766729 4089928584409552331075047)
        ·
          refine ⟨6134892876614328496612571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089928584409552331075047 6134892876614328496612571)
          ·
            refine ⟨9202339314921492744918857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134892876614328496612571 9202339314921492744918857)
            ·
              refine ⟨6901754486191119558689143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9202339314921492744918857 6901754486191119558689143)
              ·
                refine ⟨10352631729286679338033715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901754486191119558689143 10352631729286679338033715)
                ·
                  refine ⟨15528947593930019007050573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10352631729286679338033715 15528947593930019007050573)
                  ·
                    refine ⟨5823355347723757127643965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15528947593930019007050573 5823355347723757127643965)
                    ·
                      refine ⟨2183758255396408922866487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823355347723757127643965 2183758255396408922866487)
                      ·
                        rfl

theorem cell23_4252854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4252854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252854 prefixEnd_4252854 := by exact prefixLift 4252854
  have htrace : WordTrace (prefixWord ++ tailWord_4252854) baseStart_4252854 baseEnd_4252854 := by
    simpa [prefixWord, tailWord_4252854, baseEnd_4252854] using wordTrace_append hprefix tailTrace_4252854
  have hstable : (prefixWord ++ tailWord_4252854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252854).length < 2 ^ (prefixWord ++ tailWord_4252854).sum := by decide
  have hdescent : baseEnd_4252854 < baseStart_4252854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252860 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_4252860 : Nat := 118140960795 + 4252860 * 2 ^ 59
def prefixEnd_4252860 : Nat := 4983230072969 + 3 ^ 40 * 4252860 * 2
def baseEnd_4252860 : Nat := 2183761336280335899391459

theorem tailTrace_4252860 : CollatzResearch.WordTrace tailWord_4252860 prefixEnd_4252860 2183761336280335899391459 := by
  unfold tailWord_4252860
  simp only [CollatzResearch.WordTrace]
  refine ⟨77557273686311012753486017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103409698248414683671314689 77557273686311012753486017)
  ·
    refine ⟨58167955264733259565114513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77557273686311012753486017 58167955264733259565114513)
    ·
      refine ⟨43625966448549944673835885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58167955264733259565114513 43625966448549944673835885)
      ·
        refine ⟨16359737418206229252688457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43625966448549944673835885 16359737418206229252688457)
        ·
          refine ⟨12269803063654671939516343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16359737418206229252688457 12269803063654671939516343)
          ·
            refine ⟨18404704595482007909274515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12269803063654671939516343 18404704595482007909274515)
            ·
              refine ⟨27607056893223011863911773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18404704595482007909274515 27607056893223011863911773)
              ·
                refine ⟨10352646334958629448966915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27607056893223011863911773 10352646334958629448966915)
                ·
                  refine ⟨15528969502437944173450373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10352646334958629448966915 15528969502437944173450373)
                  ·
                    refine ⟨2911681781707114532521945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15528969502437944173450373 2911681781707114532521945)
                    ·
                      refine ⟨2183761336280335899391459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911681781707114532521945 2183761336280335899391459)
                      ·
                        rfl

theorem cell23_4252860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_4252860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252860 prefixEnd_4252860 := by exact prefixLift 4252860
  have htrace : WordTrace (prefixWord ++ tailWord_4252860) baseStart_4252860 baseEnd_4252860 := by
    simpa [prefixWord, tailWord_4252860, baseEnd_4252860] using wordTrace_append hprefix tailTrace_4252860
  have hstable : (prefixWord ++ tailWord_4252860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252860).length < 2 ^ (prefixWord ++ tailWord_4252860).sum := by decide
  have hdescent : baseEnd_4252860 < baseStart_4252860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4252933 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4252933 : Nat := 118140960795 + 4252933 * 2 ^ 59
def prefixEnd_4252933 : Nat := 4983230072969 + 3 ^ 40 * 4252933 * 2
def baseEnd_4252933 : Nat := 2183798820368114113778623

theorem tailTrace_4252933 : CollatzResearch.WordTrace tailWord_4252933 prefixEnd_4252933 2183798820368114113778623 := by
  unfold tailWord_4252933
  simp only [CollatzResearch.WordTrace]
  refine ⟨155117209901357558974379453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103411473267571705982919635 155117209901357558974379453)
  ·
    refine ⟨58168953713009084615392295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155117209901357558974379453 58168953713009084615392295)
    ·
      refine ⟨87253430569513626923088443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58168953713009084615392295 87253430569513626923088443)
      ·
        refine ⟨130880145854270440384632665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87253430569513626923088443 130880145854270440384632665)
        ·
          refine ⟨98160109390702830288474499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130880145854270440384632665 98160109390702830288474499)
          ·
            refine ⟨147240164086054245432711749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98160109390702830288474499 147240164086054245432711749)
            ·
              refine ⟨27607530766135171018633453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147240164086054245432711749 27607530766135171018633453)
              ·
                refine ⟨10352824037300689131987545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27607530766135171018633453 10352824037300689131987545)
                ·
                  refine ⟨7764618027975516848990659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10352824037300689131987545 7764618027975516848990659)
                  ·
                    refine ⟨11646927041963275273485989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7764618027975516848990659 11646927041963275273485989)
                    ·
                      refine ⟨2183798820368114113778623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11646927041963275273485989 2183798820368114113778623)
                      ·
                        rfl

theorem cell23_4252933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4252933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4252933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4252933 prefixEnd_4252933 := by exact prefixLift 4252933
  have htrace : WordTrace (prefixWord ++ tailWord_4252933) baseStart_4252933 baseEnd_4252933 := by
    simpa [prefixWord, tailWord_4252933, baseEnd_4252933] using wordTrace_append hprefix tailTrace_4252933
  have hstable : (prefixWord ++ tailWord_4252933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4252933).length < 2 ^ (prefixWord ++ tailWord_4252933).sum := by decide
  have hdescent : baseEnd_4252933 < baseStart_4252933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4252933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253010 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_4253010 : Nat := 118140960795 + 4253010 * 2 ^ 59
def prefixEnd_4253010 : Nat := 4983230072969 + 3 ^ 40 * 4253010 * 2
def baseEnd_4253010 : Nat := 2183838358378510312515769

theorem tailTrace_4253010 : CollatzResearch.WordTrace tailWord_4253010 prefixEnd_4253010 2183838358378510312515769 := by
  unfold tailWord_4253010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38780004580519650281233121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103413345548052400749954989 38780004580519650281233121)
  ·
    refine ⟨29085003435389737710924841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38780004580519650281233121 29085003435389737710924841)
    ·
      refine ⟨21813752576542303283193631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29085003435389737710924841 21813752576542303283193631)
      ·
        refine ⟨32720628864813454924790447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21813752576542303283193631 32720628864813454924790447)
        ·
          refine ⟨49080943297220182387185671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32720628864813454924790447 49080943297220182387185671)
          ·
            refine ⟨73621414945830273580778507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49080943297220182387185671 73621414945830273580778507)
            ·
              refine ⟨110432122418745410371167761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73621414945830273580778507 110432122418745410371167761)
              ·
                refine ⟨82824091814059057778375821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110432122418745410371167761 82824091814059057778375821)
                ·
                  refine ⟨31059034430272146666890933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82824091814059057778375821 31059034430272146666890933)
                  ·
                    refine ⟨2911784477838013750021025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31059034430272146666890933 2911784477838013750021025)
                    ·
                      refine ⟨2183838358378510312515769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911784477838013750021025 2183838358378510312515769)
                      ·
                        rfl

theorem cell23_4253010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_4253010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253010 prefixEnd_4253010 := by exact prefixLift 4253010
  have htrace : WordTrace (prefixWord ++ tailWord_4253010) baseStart_4253010 baseEnd_4253010 := by
    simpa [prefixWord, tailWord_4253010, baseEnd_4253010] using wordTrace_append hprefix tailTrace_4253010
  have hstable : (prefixWord ++ tailWord_4253010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253010).length < 2 ^ (prefixWord ++ tailWord_4253010).sum := by decide
  have hdescent : baseEnd_4253010 < baseStart_4253010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253034 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4253034 : Nat := 118140960795 + 4253034 * 2 ^ 59
def prefixEnd_4253034 : Nat := 4983230072969 + 3 ^ 40 * 4253034 * 2
def baseEnd_4253034 : Nat := 2183850681914218218615659

theorem tailTrace_4253034 : CollatzResearch.WordTrace tailWord_4253034 prefixEnd_4253034 2183850681914218218615659 := by
  unfold tailWord_4253034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38780223418497913305951539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103413929115994435482537437 38780223418497913305951539)
  ·
    refine ⟨58170335127746869958927309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38780223418497913305951539 58170335127746869958927309)
    ·
      refine ⟨21813875672905076234597741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58170335127746869958927309 21813875672905076234597741)
      ·
        refine ⟨8180203377339403587974153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21813875672905076234597741 8180203377339403587974153)
        ·
          refine ⟨6135152533004552690980615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8180203377339403587974153 6135152533004552690980615)
          ·
            refine ⟨9202728799506829036470923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135152533004552690980615 9202728799506829036470923)
            ·
              refine ⟨13804093199260243554706385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9202728799506829036470923 13804093199260243554706385)
              ·
                refine ⟨10353069899445182666029789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13804093199260243554706385 10353069899445182666029789)
                ·
                  refine ⟨3882401212291943499761171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10353069899445182666029789 3882401212291943499761171)
                  ·
                    refine ⟨5823601818437915249641757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3882401212291943499761171 5823601818437915249641757)
                    ·
                      refine ⟨2183850681914218218615659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823601818437915249641757 2183850681914218218615659)
                      ·
                        rfl

theorem cell23_4253034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4253034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253034 prefixEnd_4253034 := by exact prefixLift 4253034
  have htrace : WordTrace (prefixWord ++ tailWord_4253034) baseStart_4253034 baseEnd_4253034 := by
    simpa [prefixWord, tailWord_4253034, baseEnd_4253034] using wordTrace_append hprefix tailTrace_4253034
  have hstable : (prefixWord ++ tailWord_4253034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253034).length < 2 ^ (prefixWord ++ tailWord_4253034).sum := by decide
  have hdescent : baseEnd_4253034 < baseStart_4253034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253040 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_4253040 : Nat := 118140960795 + 4253040 * 2 ^ 59
def prefixEnd_4253040 : Nat := 4983230072969 + 3 ^ 40 * 4253040 * 2
def baseEnd_4253040 : Nat := 2183853762798145195140631

theorem tailTrace_4253040 : CollatzResearch.WordTrace tailWord_4253040 prefixEnd_4253040 2183853762798145195140631 := by
  unfold tailWord_4253040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77560556255984958124262287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103414075007979944165683049 77560556255984958124262287)
  ·
    refine ⟨116340834383977437186393431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77560556255984958124262287 116340834383977437186393431)
    ·
      refine ⟨174511251575966155779590147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116340834383977437186393431 174511251575966155779590147)
      ·
        refine ⟨261766877363949233669385221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174511251575966155779590147 261766877363949233669385221)
        ·
          refine ⟨49081289505740481313009729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261766877363949233669385221 49081289505740481313009729)
          ·
            refine ⟨36810967129305360984757297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49081289505740481313009729 36810967129305360984757297)
            ·
              refine ⟨27608225346979020738567973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36810967129305360984757297 27608225346979020738567973)
              ·
                refine ⟨5176542252558566388481495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27608225346979020738567973 5176542252558566388481495)
                ·
                  refine ⟨7764813378837849582722243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176542252558566388481495 7764813378837849582722243)
                  ·
                    refine ⟨11647220068256774374083365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7764813378837849582722243 11647220068256774374083365)
                    ·
                      refine ⟨2183853762798145195140631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11647220068256774374083365 2183853762798145195140631)
                      ·
                        rfl

theorem cell23_4253040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_4253040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253040 prefixEnd_4253040 := by exact prefixLift 4253040
  have htrace : WordTrace (prefixWord ++ tailWord_4253040) baseStart_4253040 baseEnd_4253040 := by
    simpa [prefixWord, tailWord_4253040, baseEnd_4253040] using wordTrace_append hprefix tailTrace_4253040
  have hstable : (prefixWord ++ tailWord_4253040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253040).length < 2 ^ (prefixWord ++ tailWord_4253040).sum := by decide
  have hdescent : baseEnd_4253040 < baseStart_4253040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253063 : List Nat := [1, 1, 4, 2, 2, 3, 10]
def baseStart_4253063 : Nat := 118140960795 + 4253063 * 2 ^ 59
def prefixEnd_4253063 : Nat := 4983230072969 + 3 ^ 40 * 4253063 * 2
def baseEnd_4253063 : Nat := 26961303368558007471025

theorem tailTrace_4253063 : CollatzResearch.WordTrace tailWord_4253063 prefixEnd_4253063 26961303368558007471025 := by
  unfold tailWord_4253063
  simp only [CollatzResearch.WordTrace]
  refine ⟨155121951390886591176611843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103414634260591060784407895 155121951390886591176611843)
  ·
    refine ⟨232682927086329886764917765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155121951390886591176611843 232682927086329886764917765)
    ·
      refine ⟨43628048828686853768422081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232682927086329886764917765 43628048828686853768422081)
      ·
        refine ⟨32721036621515140326316561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43628048828686853768422081 32721036621515140326316561)
        ·
          refine ⟨24540777466136355244737421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32721036621515140326316561 24540777466136355244737421)
          ·
            refine ⟨9202791549801133216776533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24540777466136355244737421 9202791549801133216776533)
            ·
              refine ⟨26961303368558007471025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9202791549801133216776533 26961303368558007471025)
              ·
                rfl

theorem cell23_4253063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 10].length) (baseStart_4253063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253063 prefixEnd_4253063 := by exact prefixLift 4253063
  have htrace : WordTrace (prefixWord ++ tailWord_4253063) baseStart_4253063 baseEnd_4253063 := by
    simpa [prefixWord, tailWord_4253063, baseEnd_4253063] using wordTrace_append hprefix tailTrace_4253063
  have hstable : (prefixWord ++ tailWord_4253063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253063).length < 2 ^ (prefixWord ++ tailWord_4253063).sum := by decide
  have hdescent : baseEnd_4253063 < baseStart_4253063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253084 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_4253084 : Nat := 118140960795 + 4253084 * 2 ^ 59
def prefixEnd_4253084 : Nat := 4983230072969 + 3 ^ 40 * 4253084 * 2
def baseEnd_4253084 : Nat := 727958785315647674330143

theorem tailTrace_4253084 : CollatzResearch.WordTrace tailWord_4253084 prefixEnd_4253084 727958785315647674330143 := by
  unfold tailWord_4253084
  simp only [CollatzResearch.WordTrace]
  refine ⟨77561358661905255881563153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103415144882540341175417537 77561358661905255881563153)
  ·
    refine ⟨58171018996428941911172365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77561358661905255881563153 58171018996428941911172365)
    ·
      refine ⟨21814132123660853216689637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58171018996428941911172365 21814132123660853216689637)
      ·
        refine ⟨4090149773186409978129307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21814132123660853216689637 4090149773186409978129307)
        ·
          refine ⟨6135224659779614967193961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090149773186409978129307 6135224659779614967193961)
          ·
            refine ⟨4601418494834711225395471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6135224659779614967193961 4601418494834711225395471)
            ·
              refine ⟨6902127742252066838093207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601418494834711225395471 6902127742252066838093207)
              ·
                refine ⟨10353191613378100257139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902127742252066838093207 10353191613378100257139811)
                ·
                  refine ⟨15529787420067150385709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10353191613378100257139811 15529787420067150385709717)
                  ·
                    refine ⟨727958785315647674330143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15529787420067150385709717 727958785315647674330143)
                    ·
                      rfl

theorem cell23_4253084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_4253084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253084 prefixEnd_4253084 := by exact prefixLift 4253084
  have htrace : WordTrace (prefixWord ++ tailWord_4253084) baseStart_4253084 baseEnd_4253084 := by
    simpa [prefixWord, tailWord_4253084, baseEnd_4253084] using wordTrace_append hprefix tailTrace_4253084
  have hstable : (prefixWord ++ tailWord_4253084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253084).length < 2 ^ (prefixWord ++ tailWord_4253084).sum := by decide
  have hdescent : baseEnd_4253084 < baseStart_4253084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253087 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4253087 : Nat := 118140960795 + 4253087 * 2 ^ 59
def prefixEnd_4253087 : Nat := 4983230072969 + 3 ^ 40 * 4253087 * 2
def baseEnd_4253087 : Nat := 2183877896388906511252915

theorem tailTrace_4253087 : CollatzResearch.WordTrace tailWord_4253087 prefixEnd_4253087 2183877896388906511252915 := by
  unfold tailWord_4253087
  simp only [CollatzResearch.WordTrace]
  refine ⟨155122826742799643275485515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103415217828533095516990343 155122826742799643275485515)
  ·
    refine ⟨232684240114199464913228273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155122826742799643275485515 232684240114199464913228273)
    ·
      refine ⟨174513180085649598684921205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232684240114199464913228273 174513180085649598684921205)
      ·
        refine ⟨16360610633029649876711363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174513180085649598684921205 16360610633029649876711363)
        ·
          refine ⟨24540915949544474815067045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16360610633029649876711363 24540915949544474815067045)
          ·
            refine ⟨4601421740539589027825071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24540915949544474815067045 4601421740539589027825071)
            ·
              refine ⟨6902132610809383541737607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601421740539589027825071 6902132610809383541737607)
              ·
                refine ⟨10353198916214075312606411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902132610809383541737607 10353198916214075312606411)
                ·
                  refine ⟨15529798374321112968909617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10353198916214075312606411 15529798374321112968909617)
                  ·
                    refine ⟨11647348780740834726682213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15529798374321112968909617 11647348780740834726682213)
                    ·
                      refine ⟨2183877896388906511252915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11647348780740834726682213 2183877896388906511252915)
                      ·
                        rfl

theorem cell23_4253087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4253087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253087 prefixEnd_4253087 := by exact prefixLift 4253087
  have htrace : WordTrace (prefixWord ++ tailWord_4253087) baseStart_4253087 baseEnd_4253087 := by
    simpa [prefixWord, tailWord_4253087, baseEnd_4253087] using wordTrace_append hprefix tailTrace_4253087
  have hstable : (prefixWord ++ tailWord_4253087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253087).length < 2 ^ (prefixWord ++ tailWord_4253087).sum := by decide
  have hdescent : baseEnd_4253087 < baseStart_4253087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253123 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 6]
def baseStart_4253123 : Nat := 118140960795 + 4253123 * 2 ^ 59
def prefixEnd_4253123 : Nat := 4983230072969 + 3 ^ 40 * 4253123 * 2
def baseEnd_4253123 : Nat := 727965460564156123467583

theorem tailTrace_4253123 : CollatzResearch.WordTrace tailWord_4253123 prefixEnd_4253123 727965460564156123467583 := by
  unfold tailWord_4253123
  simp only [CollatzResearch.WordTrace]
  refine ⟨155124139770669221423796023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103416093180446147615864015 155124139770669221423796023)
  ·
    refine ⟨232686209656003832135694035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155124139770669221423796023 232686209656003832135694035)
    ·
      refine ⟨349029314484005748203541053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232686209656003832135694035 349029314484005748203541053)
      ·
        refine ⟨130885992931502155576327895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349029314484005748203541053 130885992931502155576327895)
        ·
          refine ⟨196328989397253233364491843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130885992931502155576327895 196328989397253233364491843)
          ·
            refine ⟨294493484095879850046737765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196328989397253233364491843 294493484095879850046737765)
            ·
              refine ⟨55217528267977471883763331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294493484095879850046737765 55217528267977471883763331)
              ·
                refine ⟨82826292401966207825644997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55217528267977471883763331 82826292401966207825644997)
                ·
                  refine ⟨15529929825368663967308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82826292401966207825644997 15529929825368663967308437)
                  ·
                    refine ⟨727965460564156123467583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15529929825368663967308437 727965460564156123467583)
                    ·
                      rfl

theorem cell23_4253123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_4253123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253123 prefixEnd_4253123 := by exact prefixLift 4253123
  have htrace : WordTrace (prefixWord ++ tailWord_4253123) baseStart_4253123 baseEnd_4253123 := by
    simpa [prefixWord, tailWord_4253123, baseEnd_4253123] using wordTrace_append hprefix tailTrace_4253123
  have hstable : (prefixWord ++ tailWord_4253123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253123).length < 2 ^ (prefixWord ++ tailWord_4253123).sum := by decide
  have hdescent : baseEnd_4253123 < baseStart_4253123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253124 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4253124 : Nat := 118140960795 + 4253124 * 2 ^ 59
def prefixEnd_4253124 : Nat := 4983230072969 + 3 ^ 40 * 4253124 * 2
def baseEnd_4253124 : Nat := 2183896895173122866490245

theorem tailTrace_4253124 : CollatzResearch.WordTrace tailWord_4253124 prefixEnd_4253124 2183896895173122866490245 := by
  unfold tailWord_4253124
  simp only [CollatzResearch.WordTrace]
  refine ⟨77562088121832799297291213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103416117495777065729721617 77562088121832799297291213)
  ·
    refine ⟨29085783045687299736484205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77562088121832799297291213 29085783045687299736484205)
    ·
      refine ⟨10907168642132737401181577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29085783045687299736484205 10907168642132737401181577)
      ·
        refine ⟨8180376481599553050886183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10907168642132737401181577 8180376481599553050886183)
        ·
          refine ⟨12270564722399329576329275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180376481599553050886183 12270564722399329576329275)
          ·
            refine ⟨18405847083598994364493913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12270564722399329576329275 18405847083598994364493913)
            ·
              refine ⟨13804385312699245773370435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18405847083598994364493913 13804385312699245773370435)
              ·
                refine ⟨20706577969048868660055653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13804385312699245773370435 20706577969048868660055653)
                ·
                  refine ⟨3882483369196662873760435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20706577969048868660055653 3882483369196662873760435)
                  ·
                    refine ⟨5823725053794994310640653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3882483369196662873760435 5823725053794994310640653)
                    ·
                      refine ⟨2183896895173122866490245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5823725053794994310640653 2183896895173122866490245)
                      ·
                        rfl

theorem cell23_4253124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4253124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253124 prefixEnd_4253124 := by exact prefixLift 4253124
  have htrace : WordTrace (prefixWord ++ tailWord_4253124) baseStart_4253124 baseEnd_4253124 := by
    simpa [prefixWord, tailWord_4253124, baseEnd_4253124] using wordTrace_append hprefix tailTrace_4253124
  have hstable : (prefixWord ++ tailWord_4253124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253124).length < 2 ^ (prefixWord ++ tailWord_4253124).sum := by decide
  have hdescent : baseEnd_4253124 < baseStart_4253124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253143 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4253143 : Nat := 118140960795 + 4253143 * 2 ^ 59
def prefixEnd_4253143 : Nat := 4983230072969 + 3 ^ 40 * 4253143 * 2
def baseEnd_4253143 : Nat := 2183906651305558292152657

theorem tailTrace_4253143 : CollatzResearch.WordTrace tailWord_4253143 prefixEnd_4253143 2183906651305558292152657 := by
  unfold tailWord_4253143
  simp only [CollatzResearch.WordTrace]
  refine ⟨155124869230596764839524083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103416579487064509893016055 155124869230596764839524083)
  ·
    refine ⟨232687303845895147259286125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155124869230596764839524083 232687303845895147259286125)
    ·
      refine ⟨87257738942210680222232297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232687303845895147259286125 87257738942210680222232297)
      ·
        refine ⟨65443304206658010166674223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87257738942210680222232297 65443304206658010166674223)
        ·
          refine ⟨98164956309987015250011335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65443304206658010166674223 98164956309987015250011335)
          ·
            refine ⟨147247434464980522875017003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98164956309987015250011335 147247434464980522875017003)
            ·
              refine ⟨220871151697470784312525505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147247434464980522875017003 220871151697470784312525505)
              ·
                refine ⟨165653363773103088234394129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220871151697470784312525505 165653363773103088234394129)
                ·
                  refine ⟨124240022829827316175795597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165653363773103088234394129 124240022829827316175795597)
                  ·
                    refine ⟨46590008561185243565923349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124240022829827316175795597 46590008561185243565923349)
                    ·
                      refine ⟨2183906651305558292152657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46590008561185243565923349 2183906651305558292152657)
                      ·
                        rfl

theorem cell23_4253143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4253143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253143 prefixEnd_4253143 := by exact prefixLift 4253143
  have htrace : WordTrace (prefixWord ++ tailWord_4253143) baseStart_4253143 baseEnd_4253143 := by
    simpa [prefixWord, tailWord_4253143, baseEnd_4253143] using wordTrace_append hprefix tailTrace_4253143
  have hstable : (prefixWord ++ tailWord_4253143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253143).length < 2 ^ (prefixWord ++ tailWord_4253143).sum := by decide
  have hdescent : baseEnd_4253143 < baseStart_4253143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_4253163 : Nat := 118140960795 + 4253163 * 2 ^ 59
def prefixEnd_4253163 : Nat := 4983230072969 + 3 ^ 40 * 4253163 * 2
def baseEnd_4253163 : Nat := 2183916920918648213902565

theorem tailTrace_4253163 : CollatzResearch.WordTrace tailWord_4253163 prefixEnd_4253163 2183916920918648213902565 := by
  unfold tailWord_4253163
  simp only [CollatzResearch.WordTrace]
  refine ⟨155125598690524308255252143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103417065793682872170168095 155125598690524308255252143)
  ·
    refine ⟨232688398035786462382878215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155125598690524308255252143 232688398035786462382878215)
    ·
      refine ⟨349032597053679693574317323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232688398035786462382878215 349032597053679693574317323)
      ·
        refine ⟨523548895580519540361475985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349032597053679693574317323 523548895580519540361475985)
        ·
          refine ⟨392661671685389655271106989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523548895580519540361475985 392661671685389655271106989)
          ·
            refine ⟨147248126882021120726665121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392661671685389655271106989 147248126882021120726665121)
            ·
              refine ⟨110436095161515840544998841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147248126882021120726665121 110436095161515840544998841)
              ·
                refine ⟨82827071371136880408749131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110436095161515840544998841 82827071371136880408749131)
                ·
                  refine ⟨124240607056705320613123697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82827071371136880408749131 124240607056705320613123697)
                  ·
                    refine ⟨93180455292528990459842773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124240607056705320613123697 93180455292528990459842773)
                    ·
                      refine ⟨2183916920918648213902565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93180455292528990459842773 2183916920918648213902565)
                      ·
                        rfl

theorem cell23_4253163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_4253163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253163 prefixEnd_4253163 := by exact prefixLift 4253163
  have htrace : WordTrace (prefixWord ++ tailWord_4253163) baseStart_4253163 baseEnd_4253163 := by
    simpa [prefixWord, tailWord_4253163, baseEnd_4253163] using wordTrace_append hprefix tailTrace_4253163
  have hstable : (prefixWord ++ tailWord_4253163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253163).length < 2 ^ (prefixWord ++ tailWord_4253163).sum := by decide
  have hdescent : baseEnd_4253163 < baseStart_4253163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253181 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_4253181 : Nat := 118140960795 + 4253181 * 2 ^ 59
def prefixEnd_4253181 : Nat := 4983230072969 + 3 ^ 40 * 4253181 * 2
def baseEnd_4253181 : Nat := 2183926163570429143477483

theorem tailTrace_4253181 : CollatzResearch.WordTrace tailWord_4253181 prefixEnd_4253181 2183926163570429143477483 := by
  unfold tailWord_4253181
  simp only [CollatzResearch.WordTrace]
  refine ⟨155126255204459097329407397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103417503469639398219604931 155126255204459097329407397)
  ·
    refine ⟨29086172850836080749263887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155126255204459097329407397 29086172850836080749263887)
    ·
      refine ⟨43629259276254121123895831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29086172850836080749263887 43629259276254121123895831)
      ·
        refine ⟨65443888914381181685843747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43629259276254121123895831 65443888914381181685843747)
        ·
          refine ⟨98165833371571772528765621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65443888914381181685843747 98165833371571772528765621)
          ·
            refine ⟨9203046878584853674571777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98165833371571772528765621 9203046878584853674571777)
            ·
              refine ⟨6902285158938640255928833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9203046878584853674571777 6902285158938640255928833)
              ·
                refine ⟨5176713869203980191946625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6902285158938640255928833 5176713869203980191946625)
                ·
                  refine ⟨3882535401902985143959969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5176713869203980191946625 3882535401902985143959969)
                  ·
                    refine ⟨2911901551427238857969977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3882535401902985143959969 2911901551427238857969977)
                    ·
                      refine ⟨2183926163570429143477483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2911901551427238857969977 2183926163570429143477483)
                      ·
                        rfl

theorem cell23_4253181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_4253181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253181 prefixEnd_4253181 := by exact prefixLift 4253181
  have htrace : WordTrace (prefixWord ++ tailWord_4253181) baseStart_4253181 baseEnd_4253181 := by
    simpa [prefixWord, tailWord_4253181, baseEnd_4253181] using wordTrace_append hprefix tailTrace_4253181
  have hstable : (prefixWord ++ tailWord_4253181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253181).length < 2 ^ (prefixWord ++ tailWord_4253181).sum := by decide
  have hdescent : baseEnd_4253181 < baseStart_4253181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253204 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 7]
def baseStart_4253204 : Nat := 118140960795 + 4253204 * 2 ^ 59
def prefixEnd_4253204 : Nat := 4983230072969 + 3 ^ 40 * 4253204 * 2
def baseEnd_4253204 : Nat := 242659774847275839276653

theorem tailTrace_4253204 : CollatzResearch.WordTrace tailWord_4253204 prefixEnd_4253204 242659774847275839276653 := by
  unfold tailWord_4253204
  simp only [CollatzResearch.WordTrace]
  refine ⟨77563547041687886128747333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103418062722250514838329777 77563547041687886128747333)
  ·
    refine ⟨14543165070316478649140125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77563547041687886128747333 14543165070316478649140125)
    ·
      refine ⟨5453686901368679493427547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14543165070316478649140125 5453686901368679493427547)
      ·
        refine ⟨8180530352053019240141321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453686901368679493427547 8180530352053019240141321)
        ·
          refine ⟨6135397764039764430105991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8180530352053019240141321 6135397764039764430105991)
          ·
            refine ⟨9203096646059646645158987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135397764039764430105991 9203096646059646645158987)
            ·
              refine ⟨13804644969089469967738481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203096646059646645158987 13804644969089469967738481)
              ·
                refine ⟨10353483726817102475803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13804644969089469967738481 10353483726817102475803861)
                ·
                  refine ⟨242659774847275839276653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10353483726817102475803861 242659774847275839276653)
                  ·
                    rfl

theorem cell23_4253204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_4253204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253204 prefixEnd_4253204 := by exact prefixLift 4253204
  have htrace : WordTrace (prefixWord ++ tailWord_4253204) baseStart_4253204 baseEnd_4253204 := by
    simpa [prefixWord, tailWord_4253204, baseEnd_4253204] using wordTrace_append hprefix tailTrace_4253204
  have hstable : (prefixWord ++ tailWord_4253204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253204).length < 2 ^ (prefixWord ++ tailWord_4253204).sum := by decide
  have hdescent : baseEnd_4253204 < baseStart_4253204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253217 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_4253217 : Nat := 118140960795 + 4253217 * 2 ^ 59
def prefixEnd_4253217 : Nat := 4983230072969 + 3 ^ 40 * 4253217 * 2
def baseEnd_4253217 : Nat := 727981549624663667542439

theorem tailTrace_4253217 : CollatzResearch.WordTrace tailWord_4253217 prefixEnd_4253217 727981549624663667542439 := by
  unfold tailWord_4253217
  simp only [CollatzResearch.WordTrace]
  refine ⟨155127568232328675477717905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103418378821552450318478603 155127568232328675477717905)
  ·
    refine ⟨116345676174246506608288429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155127568232328675477717905 116345676174246506608288429)
    ·
      refine ⟨43629628565342439978108161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116345676174246506608288429 43629628565342439978108161)
      ·
        refine ⟨32722221424006829983581121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43629628565342439978108161 32722221424006829983581121)
        ·
          refine ⟨24541666068005122487685841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32722221424006829983581121 24541666068005122487685841)
          ·
            refine ⟨18406249551003841865764381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24541666068005122487685841 18406249551003841865764381)
            ·
              refine ⟨6902343581626440699661643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18406249551003841865764381 6902343581626440699661643)
              ·
                refine ⟨10353515372439661049492465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902343581626440699661643 10353515372439661049492465)
                ·
                  refine ⟨7765136529329745787119349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10353515372439661049492465 7765136529329745787119349)
                  ·
                    refine ⟨727981549624663667542439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7765136529329745787119349 727981549624663667542439)
                    ·
                      rfl

theorem cell23_4253217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_4253217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253217 prefixEnd_4253217 := by exact prefixLift 4253217
  have htrace : WordTrace (prefixWord ++ tailWord_4253217) baseStart_4253217 baseEnd_4253217 := by
    simpa [prefixWord, tailWord_4253217, baseEnd_4253217] using wordTrace_append hprefix tailTrace_4253217
  have hstable : (prefixWord ++ tailWord_4253217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253217).length < 2 ^ (prefixWord ++ tailWord_4253217).sum := by decide
  have hdescent : baseEnd_4253217 < baseStart_4253217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253247 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 3, 4]
def baseStart_4253247 : Nat := 118140960795 + 4253247 * 2 ^ 59
def prefixEnd_4253247 : Nat := 4983230072969 + 3 ^ 40 * 4253247 * 2
def baseEnd_4253247 : Nat := 727986684431208628417393

theorem tailTrace_4253247 : CollatzResearch.WordTrace tailWord_4253247 prefixEnd_4253247 727986684431208628417393 := by
  unfold tailWord_4253247
  simp only [CollatzResearch.WordTrace]
  refine ⟨155128662422219990601309995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103419108281479993734206663 155128662422219990601309995)
  ·
    refine ⟨232692993633329985901964993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155128662422219990601309995 232692993633329985901964993)
    ·
      refine ⟨174519745224997489426473745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232692993633329985901964993 174519745224997489426473745)
      ·
        refine ⟨130889808918748117069855309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174519745224997489426473745 130889808918748117069855309)
        ·
          refine ⟨49083678344530543901195741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130889808918748117069855309 49083678344530543901195741)
          ·
            refine ⟨18406379379198953962948403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49083678344530543901195741 18406379379198953962948403)
            ·
              refine ⟨27609569068798430944422605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18406379379198953962948403 27609569068798430944422605)
              ·
                refine ⟨10353588400799411604158477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27609569068798430944422605 10353588400799411604158477)
                ·
                  refine ⟨3882595650299779351559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10353588400799411604158477 3882595650299779351559429)
                  ·
                    refine ⟨727986684431208628417393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882595650299779351559429 727986684431208628417393)
                    ·
                      rfl

theorem cell23_4253247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_4253247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253247 prefixEnd_4253247 := by exact prefixLift 4253247
  have htrace : WordTrace (prefixWord ++ tailWord_4253247) baseStart_4253247 baseEnd_4253247 := by
    simpa [prefixWord, tailWord_4253247, baseEnd_4253247] using wordTrace_append hprefix tailTrace_4253247
  have hstable : (prefixWord ++ tailWord_4253247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253247).length < 2 ^ (prefixWord ++ tailWord_4253247).sum := by decide
  have hdescent : baseEnd_4253247 < baseStart_4253247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253298 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_4253298 : Nat := 118140960795 + 4253298 * 2 ^ 59
def prefixEnd_4253298 : Nat := 4983230072969 + 3 ^ 40 * 4253298 * 2
def baseEnd_4253298 : Nat := 727995413602335061904815

theorem tailTrace_4253298 : CollatzResearch.WordTrace tailWord_4253298 prefixEnd_4253298 727995413602335061904815 := by
  unfold tailWord_4253298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38782630636258806577854137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103420348363356817540944365 38782630636258806577854137)
  ·
    refine ⟨29086972977194104933390603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38782630636258806577854137 29086972977194104933390603)
    ·
      refine ⟨43630459465791157400085905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29086972977194104933390603 43630459465791157400085905)
      ·
        refine ⟨32722844599343368050064429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43630459465791157400085905 32722844599343368050064429)
        ·
          refine ⟨12271066724753763018774161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32722844599343368050064429 12271066724753763018774161)
          ·
            refine ⟨9203300043565322264080621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12271066724753763018774161 9203300043565322264080621)
            ·
              refine ⟨3451237516336995849030233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9203300043565322264080621 3451237516336995849030233)
              ·
                refine ⟨2588428137252746886772675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3451237516336995849030233 2588428137252746886772675)
                ·
                  refine ⟨3882642205879120330159013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588428137252746886772675 3882642205879120330159013)
                  ·
                    refine ⟨727995413602335061904815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882642205879120330159013 727995413602335061904815)
                    ·
                      rfl

theorem cell23_4253298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_4253298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253298 prefixEnd_4253298 := by exact prefixLift 4253298
  have htrace : WordTrace (prefixWord ++ tailWord_4253298) baseStart_4253298 baseEnd_4253298 := by
    simpa [prefixWord, tailWord_4253298, baseEnd_4253298] using wordTrace_append hprefix tailTrace_4253298
  have hstable : (prefixWord ++ tailWord_4253298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253298).length < 2 ^ (prefixWord ++ tailWord_4253298).sum := by decide
  have hdescent : baseEnd_4253298 < baseStart_4253298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253337 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_4253337 : Nat := 118140960795 + 4253337 * 2 ^ 59
def prefixEnd_4253337 : Nat := 4983230072969 + 3 ^ 40 * 4253337 * 2
def baseEnd_4253337 : Nat := 728002088850843511042255

theorem tailTrace_4253337 : CollatzResearch.WordTrace tailWord_4253337 prefixEnd_4253337 728002088850843511042255 := by
  unfold tailWord_4253337
  simp only [CollatzResearch.WordTrace]
  refine ⟨155131944991893935972086265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103421296661262623981390843 155131944991893935972086265)
  ·
    refine ⟨116348958743920451979064699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155131944991893935972086265 116348958743920451979064699)
    ·
      refine ⟨174523438115880677968597049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116348958743920451979064699 174523438115880677968597049)
      ·
        refine ⟨130892578586910508476447787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174523438115880677968597049 130892578586910508476447787)
        ·
          refine ⟨196338867880365762714671681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130892578586910508476447787 196338867880365762714671681)
          ·
            refine ⟨147254150910274322036003761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196338867880365762714671681 147254150910274322036003761)
            ·
              refine ⟨110440613182705741527002821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147254150910274322036003761 110440613182705741527002821)
              ·
                refine ⟨20707614971757326536313029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110440613182705741527002821 20707614971757326536313029)
                ·
                  refine ⟨3882677807204498725558693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20707614971757326536313029 3882677807204498725558693)
                  ·
                    refine ⟨728002088850843511042255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882677807204498725558693 728002088850843511042255)
                    ·
                      rfl

theorem cell23_4253337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_4253337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253337 prefixEnd_4253337 := by exact prefixLift 4253337
  have htrace : WordTrace (prefixWord ++ tailWord_4253337) baseStart_4253337 baseEnd_4253337 := by
    simpa [prefixWord, tailWord_4253337, baseEnd_4253337] using wordTrace_append hprefix tailTrace_4253337
  have hstable : (prefixWord ++ tailWord_4253337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253337).length < 2 ^ (prefixWord ++ tailWord_4253337).sum := by decide
  have hdescent : baseEnd_4253337 < baseStart_4253337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253367 : List Nat := [1, 1, 3, 1, 5, 1, 3, 8]
def baseStart_4253367 : Nat := 118140960795 + 4253367 * 2 ^ 59
def prefixEnd_4253367 : Nat := 4983230072969 + 3 ^ 40 * 4253367 * 2
def baseEnd_4253367 : Nat := 80889691517487607990801

theorem tailTrace_4253367 : CollatzResearch.WordTrace tailWord_4253367 prefixEnd_4253367 80889691517487607990801 := by
  unfold tailWord_4253367
  simp only [CollatzResearch.WordTrace]
  refine ⟨155133039181785251095678355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103422026121190167397118903 155133039181785251095678355)
  ·
    refine ⟨232699558772677876643517533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155133039181785251095678355 232699558772677876643517533)
    ·
      refine ⟨87262334539754203741319075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232699558772677876643517533 87262334539754203741319075)
      ·
        refine ⟨130893501809631305611978613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87262334539754203741319075 130893501809631305611978613)
        ·
          refine ⟨12271265794652934901122995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130893501809631305611978613 12271265794652934901122995)
          ·
            refine ⟨18406898691979402351684493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12271265794652934901122995 18406898691979402351684493)
            ·
              refine ⟨6902587009492275881881685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18406898691979402351684493 6902587009492275881881685)
              ·
                refine ⟨80889691517487607990801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6902587009492275881881685 80889691517487607990801)
                ·
                  rfl

theorem cell23_4253367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 8].length) (baseStart_4253367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253367 prefixEnd_4253367 := by exact prefixLift 4253367
  have htrace : WordTrace (prefixWord ++ tailWord_4253367) baseStart_4253367 baseEnd_4253367 := by
    simpa [prefixWord, tailWord_4253367, baseEnd_4253367] using wordTrace_append hprefix tailTrace_4253367
  have hstable : (prefixWord ++ tailWord_4253367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253367).length < 2 ^ (prefixWord ++ tailWord_4253367).sum := by decide
  have hdescent : baseEnd_4253367 < baseStart_4253367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253374 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4253374 : Nat := 118140960795 + 4253374 * 2 ^ 59
def prefixEnd_4253374 : Nat := 4983230072969 + 3 ^ 40 * 4253374 * 2
def baseEnd_4253374 : Nat := 2184025265336746888364095

theorem tailTrace_4253374 : CollatzResearch.WordTrace tailWord_4253374 prefixEnd_4253374 2184025265336746888364095 := by
  unfold tailWord_4253374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19391661811594986411397897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103422196328506594194122117 19391661811594986411397897)
  ·
    refine ⟨14543746358696239808548423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19391661811594986411397897 14543746358696239808548423)
    ·
      refine ⟨21815619538044359712822635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14543746358696239808548423 21815619538044359712822635)
      ·
        refine ⟨32723429307066539569233953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21815619538044359712822635 32723429307066539569233953)
        ·
          refine ⟨24542571980299904676925465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32723429307066539569233953 24542571980299904676925465)
          ·
            refine ⟨18406928985224928507694099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24542571980299904676925465 18406928985224928507694099)
            ·
              refine ⟨27610393477837392761541149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18406928985224928507694099 27610393477837392761541149)
              ·
                refine ⟨10353897554189022285577931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27610393477837392761541149 10353897554189022285577931)
                ·
                  refine ⟨15530846331283533428366897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10353897554189022285577931 15530846331283533428366897)
                  ·
                    refine ⟨11648134748462650071275173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15530846331283533428366897 11648134748462650071275173)
                    ·
                      refine ⟨2184025265336746888364095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11648134748462650071275173 2184025265336746888364095)
                      ·
                        rfl

theorem cell23_4253374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4253374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253374 prefixEnd_4253374 := by exact prefixLift 4253374
  have htrace : WordTrace (prefixWord ++ tailWord_4253374) baseStart_4253374 baseEnd_4253374 := by
    simpa [prefixWord, tailWord_4253374, baseEnd_4253374] using wordTrace_append hprefix tailTrace_4253374
  have hstable : (prefixWord ++ tailWord_4253374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253374).length < 2 ^ (prefixWord ++ tailWord_4253374).sum := by decide
  have hdescent : baseEnd_4253374 < baseStart_4253374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253382 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4253382 : Nat := 118140960795 + 4253382 * 2 ^ 59
def prefixEnd_4253382 : Nat := 4983230072969 + 3 ^ 40 * 4253382 * 2
def baseEnd_4253382 : Nat := 2184029373181982857064059

theorem tailTrace_4253382 : CollatzResearch.WordTrace tailWord_4253382 prefixEnd_4253382 2184029373181982857064059 := by
  unfold tailWord_4253382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847924571147840895546075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103422390851153939104982933 4847924571147840895546075)
  ·
    refine ⟨7271886856721761343319113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4847924571147840895546075 7271886856721761343319113)
    ·
      refine ⟨5453915142541321007489335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7271886856721761343319113 5453915142541321007489335)
      ·
        refine ⟨8180872713811981511234003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453915142541321007489335 8180872713811981511234003)
        ·
          refine ⟨12271309070717972266851005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180872713811981511234003 12271309070717972266851005)
          ·
            refine ⟨4601740901519239600069127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12271309070717972266851005 4601740901519239600069127)
            ·
              refine ⟨6902611352278859400103691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601740901519239600069127 6902611352278859400103691)
              ·
                refine ⟨10353917028418289100155537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902611352278859400103691 10353917028418289100155537)
                ·
                  refine ⟨7765437771313716825116653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10353917028418289100155537 7765437771313716825116653)
                  ·
                    refine ⟨2912039164242643809418745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7765437771313716825116653 2912039164242643809418745)
                    ·
                      refine ⟨2184029373181982857064059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912039164242643809418745 2184029373181982857064059)
                      ·
                        rfl

theorem cell23_4253382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4253382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253382 prefixEnd_4253382 := by exact prefixLift 4253382
  have htrace : WordTrace (prefixWord ++ tailWord_4253382) baseStart_4253382 baseEnd_4253382 := by
    simpa [prefixWord, tailWord_4253382, baseEnd_4253382] using wordTrace_append hprefix tailTrace_4253382
  have hstable : (prefixWord ++ tailWord_4253382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253382).length < 2 ^ (prefixWord ++ tailWord_4253382).sum := by decide
  have hdescent : baseEnd_4253382 < baseStart_4253382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253405 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4253405 : Nat := 118140960795 + 4253405 * 2 ^ 59
def prefixEnd_4253405 : Nat := 4983230072969 + 3 ^ 40 * 4253405 * 2
def baseEnd_4253405 : Nat := 728013727745678755692151

theorem tailTrace_4253405 : CollatzResearch.WordTrace tailWord_4253405 prefixEnd_4253405 728013727745678755692151 := by
  unfold tailWord_4253405
  simp only [CollatzResearch.WordTrace]
  refine ⟨155134425155647583585561669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103422950103765055723707779 155134425155647583585561669)
  ·
    refine ⟨29087704716683921922292813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155134425155647583585561669 29087704716683921922292813)
    ·
      refine ⟨10907889268756470720859805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29087704716683921922292813 10907889268756470720859805)
      ·
        refine ⟨4090458475783676520322427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10907889268756470720859805 4090458475783676520322427)
        ·
          refine ⟨6135687713675514780483641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090458475783676520322427 6135687713675514780483641)
          ·
            refine ⟨4601765785256636085362731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6135687713675514780483641 4601765785256636085362731)
            ·
              refine ⟨6902648677884954128044097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601765785256636085362731 6902648677884954128044097)
              ·
                refine ⟨5176986508413715596033073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6902648677884954128044097 5176986508413715596033073)
                ·
                  refine ⟨3882739881310286697024805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5176986508413715596033073 3882739881310286697024805)
                  ·
                    refine ⟨728013727745678755692151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882739881310286697024805 728013727745678755692151)
                    ·
                      rfl

theorem cell23_4253405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4253405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253405 prefixEnd_4253405 := by exact prefixLift 4253405
  have htrace : WordTrace (prefixWord ++ tailWord_4253405) baseStart_4253405 baseEnd_4253405 := by
    simpa [prefixWord, tailWord_4253405, baseEnd_4253405] using wordTrace_append hprefix tailTrace_4253405
  have hstable : (prefixWord ++ tailWord_4253405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253405).length < 2 ^ (prefixWord ++ tailWord_4253405).sum := by decide
  have hdescent : baseEnd_4253405 < baseStart_4253405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253427 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 6]
def baseStart_4253427 : Nat := 118140960795 + 4253427 * 2 ^ 59
def prefixEnd_4253427 : Nat := 4983230072969 + 3 ^ 40 * 4253427 * 2
def baseEnd_4253427 : Nat := 728017493270478393667117

theorem tailTrace_4253427 : CollatzResearch.WordTrace tailWord_4253427 prefixEnd_4253427 728017493270478393667117 := by
  unfold tailWord_4253427
  simp only [CollatzResearch.WordTrace]
  refine ⟨155135227561567881342862535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103423485041045254228575023 155135227561567881342862535)
  ·
    refine ⟨232702841342351822014293803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155135227561567881342862535 232702841342351822014293803)
    ·
      refine ⟨349054262013527733021440705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232702841342351822014293803 349054262013527733021440705)
      ·
        refine ⟨261790696510145799766080529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349054262013527733021440705 261790696510145799766080529)
        ·
          refine ⟨196343022382609349824560397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261790696510145799766080529 196343022382609349824560397)
          ·
            refine ⟨73628633393478506184210149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196343022382609349824560397 73628633393478506184210149)
            ·
              refine ⟨13805368761277219909539403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73628633393478506184210149 13805368761277219909539403)
              ·
                refine ⟨20708053141915829864309105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13805368761277219909539403 20708053141915829864309105)
                ·
                  refine ⟨15531039856436872398231829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20708053141915829864309105 15531039856436872398231829)
                  ·
                    refine ⟨728017493270478393667117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15531039856436872398231829 728017493270478393667117)
                    ·
                      rfl

theorem cell23_4253427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_4253427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253427 prefixEnd_4253427 := by exact prefixLift 4253427
  have htrace : WordTrace (prefixWord ++ tailWord_4253427) baseStart_4253427 baseEnd_4253427 := by
    simpa [prefixWord, tailWord_4253427, baseEnd_4253427] using wordTrace_append hprefix tailTrace_4253427
  have hstable : (prefixWord ++ tailWord_4253427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253427).length < 2 ^ (prefixWord ++ tailWord_4253427).sum := by decide
  have hdescent : baseEnd_4253427 < baseStart_4253427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253451 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 4, 2, 2]
def baseStart_4253451 : Nat := 118140960795 + 4253451 * 2 ^ 59
def prefixEnd_4253451 : Nat := 4983230072969 + 3 ^ 40 * 4253451 * 2
def baseEnd_4253451 : Nat := 2184064803347143087101241

theorem tailTrace_4253451 : CollatzResearch.WordTrace tailWord_4253451 prefixEnd_4253451 2184064803347143087101241 := by
  unfold tailWord_4253451
  simp only [CollatzResearch.WordTrace]
  refine ⟨155136102913480933441736207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103424068608987288961157471 155136102913480933441736207)
  ·
    refine ⟨232704154370221400162604311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155136102913480933441736207 232704154370221400162604311)
    ·
      refine ⟨349056231555332100243906467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232704154370221400162604311 349056231555332100243906467)
      ·
        refine ⟨523584347332998150365859701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349056231555332100243906467 523584347332998150365859701)
        ·
          refine ⟨49086032562468576596799347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 523584347332998150365859701 49086032562468576596799347)
          ·
            refine ⟨73629048843702864895199021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49086032562468576596799347 73629048843702864895199021)
            ·
              refine ⟨27610893316388574335699633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73629048843702864895199021 27610893316388574335699633)
              ·
                refine ⟨20708169987291430751774725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27610893316388574335699633 20708169987291430751774725)
                ·
                  refine ⟨3882781872617143265957761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20708169987291430751774725 3882781872617143265957761)
                  ·
                    refine ⟨2912086404462857449468321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3882781872617143265957761 2912086404462857449468321)
                    ·
                      refine ⟨2184064803347143087101241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912086404462857449468321 2184064803347143087101241)
                      ·
                        rfl

theorem cell23_4253451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2, 2].length) (baseStart_4253451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253451 prefixEnd_4253451 := by exact prefixLift 4253451
  have htrace : WordTrace (prefixWord ++ tailWord_4253451) baseStart_4253451 baseEnd_4253451 := by
    simpa [prefixWord, tailWord_4253451, baseEnd_4253451] using wordTrace_append hprefix tailTrace_4253451
  have hstable : (prefixWord ++ tailWord_4253451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253451).length < 2 ^ (prefixWord ++ tailWord_4253451).sum := by decide
  have hdescent : baseEnd_4253451 < baseStart_4253451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253468 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4253468 : Nat := 118140960795 + 4253468 * 2 ^ 59
def prefixEnd_4253468 : Nat := 4983230072969 + 3 ^ 40 * 4253468 * 2
def baseEnd_4253468 : Nat := 2184073532518269520588663

theorem tailTrace_4253468 : CollatzResearch.WordTrace tailWord_4253468 prefixEnd_4253468 2184073532518269520588663 := by
  unfold tailWord_4253468
  simp only [CollatzResearch.WordTrace]
  refine ⟨77568361477209672672552529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103424481969612896896736705 77568361477209672672552529)
  ·
    refine ⟨58176271107907254504414397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77568361477209672672552529 58176271107907254504414397)
    ·
      refine ⟨21816101665465220439155399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58176271107907254504414397 21816101665465220439155399)
      ·
        refine ⟨32724152498197830658733099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21816101665465220439155399 32724152498197830658733099)
        ·
          refine ⟨49086228747296745988099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32724152498197830658733099 49086228747296745988099649)
          ·
            refine ⟨36814671560472559491074737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49086228747296745988099649 36814671560472559491074737)
            ·
              refine ⟨27611003670354419618306053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36814671560472559491074737 27611003670354419618306053)
              ·
                refine ⟨5177063188191453678432385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27611003670354419618306053 5177063188191453678432385)
                ·
                  refine ⟨3882797391143590258824289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5177063188191453678432385 3882797391143590258824289)
                  ·
                    refine ⟨2912098043357692694118217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3882797391143590258824289 2912098043357692694118217)
                    ·
                      refine ⟨2184073532518269520588663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912098043357692694118217 2184073532518269520588663)
                      ·
                        rfl

theorem cell23_4253468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4253468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253468 prefixEnd_4253468 := by exact prefixLift 4253468
  have htrace : WordTrace (prefixWord ++ tailWord_4253468) baseStart_4253468 baseEnd_4253468 := by
    simpa [prefixWord, tailWord_4253468, baseEnd_4253468] using wordTrace_append hprefix tailTrace_4253468
  have hstable : (prefixWord ++ tailWord_4253468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253468).length < 2 ^ (prefixWord ++ tailWord_4253468).sum := by decide
  have hdescent : baseEnd_4253468 < baseStart_4253468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253547 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 10]
def baseStart_4253547 : Nat := 118140960795 + 4253547 * 2 ^ 59
def prefixEnd_4253547 : Nat := 4983230072969 + 3 ^ 40 * 4253547 * 2
def baseEnd_4253547 : Nat := 242679344165552745722311

theorem tailTrace_4253547 : CollatzResearch.WordTrace tailWord_4253547 prefixEnd_4253547 242679344165552745722311 := by
  unfold tailWord_4253547
  simp only [CollatzResearch.WordTrace]
  refine ⟨155139604321133141837230895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103426402880755427891487263 155139604321133141837230895)
  ·
    refine ⟨232709406481699712755846343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155139604321133141837230895 232709406481699712755846343)
    ·
      refine ⟨349064109722549569133769515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232709406481699712755846343 349064109722549569133769515)
      ·
        refine ⟨523596164583824353700654273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349064109722549569133769515 523596164583824353700654273)
        ·
          refine ⟨392697123437868265275490705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523596164583824353700654273 392697123437868265275490705)
          ·
            refine ⟨294522842578401198956618029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392697123437868265275490705 294522842578401198956618029)
            ·
              refine ⟨110446065966900449608731761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294522842578401198956618029 110446065966900449608731761)
              ·
                refine ⟨82834549475175337206548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110446065966900449608731761 82834549475175337206548821)
                ·
                  refine ⟨242679344165552745722311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82834549475175337206548821 242679344165552745722311)
                  ·
                    rfl

theorem cell23_4253547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_4253547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253547 prefixEnd_4253547 := by exact prefixLift 4253547
  have htrace : WordTrace (prefixWord ++ tailWord_4253547) baseStart_4253547 baseEnd_4253547 := by
    simpa [prefixWord, tailWord_4253547, baseEnd_4253547] using wordTrace_append hprefix tailTrace_4253547
  have hstable : (prefixWord ++ tailWord_4253547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253547).length < 2 ^ (prefixWord ++ tailWord_4253547).sum := by decide
  have hdescent : baseEnd_4253547 < baseStart_4253547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253558 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4253558 : Nat := 118140960795 + 4253558 * 2 ^ 59
def prefixEnd_4253558 : Nat := 4983230072969 + 3 ^ 40 * 4253558 * 2
def baseEnd_4253558 : Nat := 2184119745777174168463249

theorem tailTrace_4253558 : CollatzResearch.WordTrace tailWord_4253558 prefixEnd_4253558 2184119745777174168463249 := by
  unfold tailWord_4253558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696250345255830669742583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103426670349395527143920885 9696250345255830669742583)
  ·
    refine ⟨14544375517883746004613875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9696250345255830669742583 14544375517883746004613875)
    ·
      refine ⟨21816563276825619006920813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14544375517883746004613875 21816563276825619006920813)
      ·
        refine ⟨8181211228809607127595305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21816563276825619006920813 8181211228809607127595305)
        ·
          refine ⟨6135908421607205345696479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8181211228809607127595305 6135908421607205345696479)
          ·
            refine ⟨9203862632410808018544719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135908421607205345696479 9203862632410808018544719)
            ·
              refine ⟨13805793948616212027817079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203862632410808018544719 13805793948616212027817079)
              ·
                refine ⟨20708690922924318041725619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13805793948616212027817079 20708690922924318041725619)
                ·
                  refine ⟨31063036384386477062588429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20708690922924318041725619 31063036384386477062588429)
                  ·
                    refine ⟨11648638644144928898470661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31063036384386477062588429 11648638644144928898470661)
                    ·
                      refine ⟨2184119745777174168463249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11648638644144928898470661 2184119745777174168463249)
                      ·
                        rfl

theorem cell23_4253558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4253558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253558 prefixEnd_4253558 := by exact prefixLift 4253558
  have htrace : WordTrace (prefixWord ++ tailWord_4253558) baseStart_4253558 baseEnd_4253558 := by
    simpa [prefixWord, tailWord_4253558, baseEnd_4253558] using wordTrace_append hprefix tailTrace_4253558
  have hstable : (prefixWord ++ tailWord_4253558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253558).length < 2 ^ (prefixWord ++ tailWord_4253558).sum := by decide
  have hdescent : baseEnd_4253558 < baseStart_4253558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253568 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 1, 4]
def baseStart_4253568 : Nat := 118140960795 + 4253568 * 2 ^ 59
def prefixEnd_4253568 : Nat := 4983230072969 + 3 ^ 40 * 4253568 * 2
def baseEnd_4253568 : Nat := 728041626861239709779401

theorem tailTrace_4253568 : CollatzResearch.WordTrace tailWord_4253568 prefixEnd_4253568 728041626861239709779401 := by
  unfold tailWord_4253568
  simp only [CollatzResearch.WordTrace]
  refine ⟨77570185127028531211872679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103426913502704708282496905 77570185127028531211872679)
  ·
    refine ⟨116355277690542796817809019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77570185127028531211872679 116355277690542796817809019)
    ·
      refine ⟨174532916535814195226713529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116355277690542796817809019 174532916535814195226713529)
      ·
        refine ⟨130899687401860646420035147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174532916535814195226713529 130899687401860646420035147)
        ·
          refine ⟨196349531102790969630052721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130899687401860646420035147 196349531102790969630052721)
          ·
            refine ⟨147262148327093227222539541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196349531102790969630052721 147262148327093227222539541)
            ·
              refine ⟨6902913202832495026056541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147262148327093227222539541 6902913202832495026056541)
              ·
                refine ⟨2588592451062185634771203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6902913202832495026056541 2588592451062185634771203)
                ·
                  refine ⟨3882888676593278452156805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588592451062185634771203 3882888676593278452156805)
                  ·
                    refine ⟨728041626861239709779401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882888676593278452156805 728041626861239709779401)
                    ·
                      rfl

theorem cell23_4253568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_4253568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253568 prefixEnd_4253568 := by exact prefixLift 4253568
  have htrace : WordTrace (prefixWord ++ tailWord_4253568) baseStart_4253568 baseEnd_4253568 := by
    simpa [prefixWord, tailWord_4253568, baseEnd_4253568] using wordTrace_append hprefix tailTrace_4253568
  have hstable : (prefixWord ++ tailWord_4253568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253568).length < 2 ^ (prefixWord ++ tailWord_4253568).sum := by decide
  have hdescent : baseEnd_4253568 < baseStart_4253568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253624 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_4253624 : Nat := 118140960795 + 4253624 * 2 ^ 59
def prefixEnd_4253624 : Nat := 4983230072969 + 3 ^ 40 * 4253624 * 2
def baseEnd_4253624 : Nat := 728051211833456970079315

theorem tailTrace_4253624 : CollatzResearch.WordTrace tailWord_4253624 prefixEnd_4253624 728051211833456970079315 := by
  unfold tailWord_4253624
  simp only [CollatzResearch.WordTrace]
  refine ⟨77571206370927091993891963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103428275161236122658522617 77571206370927091993891963)
  ·
    refine ⟨116356809556390637990837945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77571206370927091993891963 116356809556390637990837945)
    ·
      refine ⟨87267607167292978493128459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116356809556390637990837945 87267607167292978493128459)
      ·
        refine ⟨130901410750939467739692689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87267607167292978493128459 130901410750939467739692689)
        ·
          refine ⟨98176058063204600804769517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130901410750939467739692689 98176058063204600804769517)
          ·
            refine ⟨36816021773701725301788569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98176058063204600804769517 36816021773701725301788569)
            ·
              refine ⟨27612016330276293976341427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36816021773701725301788569 27612016330276293976341427)
              ·
                refine ⟨41418024495414440964512141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27612016330276293976341427 41418024495414440964512141)
                ·
                  refine ⟨15531759185780415361692053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41418024495414440964512141 15531759185780415361692053)
                  ·
                    refine ⟨728051211833456970079315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15531759185780415361692053 728051211833456970079315)
                    ·
                      rfl

theorem cell23_4253624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_4253624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253624 prefixEnd_4253624 := by exact prefixLift 4253624
  have htrace : WordTrace (prefixWord ++ tailWord_4253624) baseStart_4253624 baseEnd_4253624 := by
    simpa [prefixWord, tailWord_4253624, baseEnd_4253624] using wordTrace_append hprefix tailTrace_4253624
  have hstable : (prefixWord ++ tailWord_4253624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253624).length < 2 ^ (prefixWord ++ tailWord_4253624).sum := by decide
  have hdescent : baseEnd_4253624 < baseStart_4253624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253631 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_4253631 : Nat := 118140960795 + 4253631 * 2 ^ 59
def prefixEnd_4253631 : Nat := 4983230072969 + 3 ^ 40 * 4253631 * 2
def baseEnd_4253631 : Nat := 2184157229864952382850413

theorem tailTrace_4253631 : CollatzResearch.WordTrace tailWord_4253631 prefixEnd_4253631 2184157229864952382850413 := by
  unfold tailWord_4253631
  simp only [CollatzResearch.WordTrace]
  refine ⟨155142668052828824183288747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103428445368552549455525831 155142668052828824183288747)
  ·
    refine ⟨232714002079243236274933121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155142668052828824183288747 232714002079243236274933121)
    ·
      refine ⟨174535501559432427206199841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232714002079243236274933121 174535501559432427206199841)
      ·
        refine ⟨130901626169574320404649881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174535501559432427206199841 130901626169574320404649881)
        ·
          refine ⟨98176219627180740303487411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130901626169574320404649881 98176219627180740303487411)
          ·
            refine ⟨147264329440771110455231117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98176219627180740303487411 147264329440771110455231117)
            ·
              refine ⟨55224123540289166420711669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147264329440771110455231117 55224123540289166420711669)
              ·
                refine ⟨5177261581902109351941719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55224123540289166420711669 5177261581902109351941719)
                ·
                  refine ⟨7765892372853164027912579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177261581902109351941719 7765892372853164027912579)
                  ·
                    refine ⟨11648838559279746041868869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7765892372853164027912579 11648838559279746041868869)
                    ·
                      refine ⟨2184157229864952382850413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11648838559279746041868869 2184157229864952382850413)
                      ·
                        rfl

theorem cell23_4253631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_4253631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253631 prefixEnd_4253631 := by exact prefixLift 4253631
  have htrace : WordTrace (prefixWord ++ tailWord_4253631) baseStart_4253631 baseEnd_4253631 := by
    simpa [prefixWord, tailWord_4253631, baseEnd_4253631] using wordTrace_append hprefix tailTrace_4253631
  have hstable : (prefixWord ++ tailWord_4253631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253631).length < 2 ^ (prefixWord ++ tailWord_4253631).sum := by decide
  have hdescent : baseEnd_4253631 < baseStart_4253631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253678 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4253678 : Nat := 118140960795 + 4253678 * 2 ^ 59
def prefixEnd_4253678 : Nat := 4983230072969 + 3 ^ 40 * 4253678 * 2
def baseEnd_4253678 : Nat := 2184181363455713698962697

theorem tailTrace_4253678 : CollatzResearch.WordTrace tailWord_4253678 prefixEnd_4253678 2184181363455713698962697 := by
  unfold tailWord_4253678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19393047785457318901281211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103429588189105700806833125 19393047785457318901281211)
  ·
    refine ⟨29089571678185978351921817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19393047785457318901281211 29089571678185978351921817)
    ·
      refine ⟨21817178758639483763941363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29089571678185978351921817 21817178758639483763941363)
      ·
        refine ⟨32725768137959225645912045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21817178758639483763941363 32725768137959225645912045)
        ·
          refine ⟨12272163051734709617217017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32725768137959225645912045 12272163051734709617217017)
          ·
            refine ⟨9204122288801032212912763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12272163051734709617217017 9204122288801032212912763)
            ·
              refine ⟨13806183433201548319369145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204122288801032212912763 13806183433201548319369145)
              ·
                refine ⟨10354637574901161239526859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13806183433201548319369145 10354637574901161239526859)
                ·
                  refine ⟨15531956362351741859290289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10354637574901161239526859 15531956362351741859290289)
                  ·
                    refine ⟨11648967271763806394467717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15531956362351741859290289 11648967271763806394467717)
                    ·
                      refine ⟨2184181363455713698962697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11648967271763806394467717 2184181363455713698962697)
                      ·
                        rfl

theorem cell23_4253678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4253678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253678 prefixEnd_4253678 := by exact prefixLift 4253678
  have htrace : WordTrace (prefixWord ++ tailWord_4253678) baseStart_4253678 baseEnd_4253678 := by
    simpa [prefixWord, tailWord_4253678, baseEnd_4253678] using wordTrace_append hprefix tailTrace_4253678
  have hstable : (prefixWord ++ tailWord_4253678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253678).length < 2 ^ (prefixWord ++ tailWord_4253678).sum := by decide
  have hdescent : baseEnd_4253678 < baseStart_4253678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253708 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_4253708 : Nat := 118140960795 + 4253708 * 2 ^ 59
def prefixEnd_4253708 : Nat := 4983230072969 + 3 ^ 40 * 4253708 * 2
def baseEnd_4253708 : Nat := 2184196767875348581587559

theorem tailTrace_4253708 : CollatzResearch.WordTrace tailWord_4253708 prefixEnd_4253708 2184196767875348581587559 := by
  unfold tailWord_4253708
  simp only [CollatzResearch.WordTrace]
  refine ⟨77572738236774933166920889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103430317649033244222561185 77572738236774933166920889)
  ·
    refine ⟨58179553677581199875190667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77572738236774933166920889 58179553677581199875190667)
    ·
      refine ⟨87269330516371799812786001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58179553677581199875190667 87269330516371799812786001)
      ·
        refine ⟨65451997887278849859589501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87269330516371799812786001 65451997887278849859589501)
        ·
          refine ⟨24544499207729568697346063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65451997887278849859589501 24544499207729568697346063)
          ·
            refine ⟨36816748811594353046019095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24544499207729568697346063 36816748811594353046019095)
            ·
              refine ⟨55225123217391529569028643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36816748811594353046019095 55225123217391529569028643)
              ·
                refine ⟨82837684826087294353542965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55225123217391529569028643 82837684826087294353542965)
                ·
                  refine ⟨7766032952445683845644653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82837684826087294353542965 7766032952445683845644653)
                  ·
                    refine ⟨2912262357167131442116745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7766032952445683845644653 2912262357167131442116745)
                    ·
                      refine ⟨2184196767875348581587559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912262357167131442116745 2184196767875348581587559)
                      ·
                        rfl

theorem cell23_4253708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_4253708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253708 prefixEnd_4253708 := by exact prefixLift 4253708
  have htrace : WordTrace (prefixWord ++ tailWord_4253708) baseStart_4253708 baseEnd_4253708 := by
    simpa [prefixWord, tailWord_4253708, baseEnd_4253708] using wordTrace_append hprefix tailTrace_4253708
  have hstable : (prefixWord ++ tailWord_4253708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253708).length < 2 ^ (prefixWord ++ tailWord_4253708).sum := by decide
  have hdescent : baseEnd_4253708 < baseStart_4253708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253725 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4253725 : Nat := 118140960795 + 4253725 * 2 ^ 59
def prefixEnd_4253725 : Nat := 4983230072969 + 3 ^ 40 * 4253725 * 2
def baseEnd_4253725 : Nat := 2184205497046475015074981

theorem tailTrace_4253725 : CollatzResearch.WordTrace tailWord_4253725 prefixEnd_4253725 2184205497046475015074981 := by
  unfold tailWord_4253725
  simp only [CollatzResearch.WordTrace]
  refine ⟨155146096514488278237210629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103430731009658852158140419 155146096514488278237210629)
  ·
    refine ⟨29089893096466552169476993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155146096514488278237210629 29089893096466552169476993)
    ·
      refine ⟨21817419822349914127107745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29089893096466552169476993 21817419822349914127107745)
      ·
        refine ⟨16363064866762435595330809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21817419822349914127107745 16363064866762435595330809)
        ·
          refine ⟨12272298650071826696498107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16363064866762435595330809 12272298650071826696498107)
          ·
            refine ⟨18408447975107740044747161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12272298650071826696498107 18408447975107740044747161)
            ·
              refine ⟨13806335981330805033560371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18408447975107740044747161 13806335981330805033560371)
              ·
                refine ⟨20709503971996207550340557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13806335981330805033560371 20709503971996207550340557)
                ·
                  refine ⟨7766063989498577831377709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20709503971996207550340557 7766063989498577831377709)
                  ·
                    refine ⟨2912273996061966686766641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7766063989498577831377709 2912273996061966686766641)
                    ·
                      refine ⟨2184205497046475015074981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912273996061966686766641 2184205497046475015074981)
                      ·
                        rfl

theorem cell23_4253725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4253725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253725 prefixEnd_4253725 := by exact prefixLift 4253725
  have htrace : WordTrace (prefixWord ++ tailWord_4253725) baseStart_4253725 baseEnd_4253725 := by
    simpa [prefixWord, tailWord_4253725, baseEnd_4253725] using wordTrace_append hprefix tailTrace_4253725
  have hstable : (prefixWord ++ tailWord_4253725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253725).length < 2 ^ (prefixWord ++ tailWord_4253725).sum := by decide
  have hdescent : baseEnd_4253725 < baseStart_4253725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253736 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4253736 : Nat := 118140960795 + 4253736 * 2 ^ 59
def prefixEnd_4253736 : Nat := 4983230072969 + 3 ^ 40 * 4253736 * 2
def baseEnd_4253736 : Nat := 2184211145333674472037431

theorem tailTrace_4253736 : CollatzResearch.WordTrace tailWord_4253736 prefixEnd_4253736 2184211145333674472037431 := by
  unfold tailWord_4253736
  simp only [CollatzResearch.WordTrace]
  refine ⟨77573248858724213557930531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103430998478298951410574041 77573248858724213557930531)
  ·
    refine ⟨116359873288086320336895797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77573248858724213557930531 116359873288086320336895797)
    ·
      refine ⟨10908738120758092531583981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116359873288086320336895797 10908738120758092531583981)
      ·
        refine ⟨4090776795284284699343993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10908738120758092531583981 4090776795284284699343993)
        ·
          refine ⟨3068082596463213524507995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4090776795284284699343993 3068082596463213524507995)
          ·
            refine ⟨4602123894694820286761993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068082596463213524507995 4602123894694820286761993)
            ·
              refine ⟨3451592921021115215071495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602123894694820286761993 3451592921021115215071495)
              ·
                refine ⟨5177389381531672822607243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451592921021115215071495 5177389381531672822607243)
                ·
                  refine ⟨7766084072297509233910865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177389381531672822607243 7766084072297509233910865)
                  ·
                    refine ⟨5824563054223131925433149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7766084072297509233910865 5824563054223131925433149)
                    ·
                      refine ⟨2184211145333674472037431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5824563054223131925433149 2184211145333674472037431)
                      ·
                        rfl

theorem cell23_4253736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4253736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253736 prefixEnd_4253736 := by exact prefixLift 4253736
  have htrace : WordTrace (prefixWord ++ tailWord_4253736) baseStart_4253736 baseEnd_4253736 := by
    simpa [prefixWord, tailWord_4253736, baseEnd_4253736] using wordTrace_append hprefix tailTrace_4253736
  have hstable : (prefixWord ++ tailWord_4253736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253736).length < 2 ^ (prefixWord ++ tailWord_4253736).sum := by decide
  have hdescent : baseEnd_4253736 < baseStart_4253736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253742 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4253742 : Nat := 118140960795 + 4253742 * 2 ^ 59
def prefixEnd_4253742 : Nat := 4983230072969 + 3 ^ 40 * 4253742 * 2
def baseEnd_4253742 : Nat := 2184214226217601448562403

theorem tailTrace_4253742 : CollatzResearch.WordTrace tailWord_4253742 prefixEnd_4253742 2184214226217601448562403 := by
  unfold tailWord_4253742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19393339569428336267572435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103431144370284460093719653 19393339569428336267572435)
  ·
    refine ⟨29090009354142504401358653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19393339569428336267572435 29090009354142504401358653)
    ·
      refine ⟨10908753507803439150509495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29090009354142504401358653 10908753507803439150509495)
      ·
        refine ⟨16363130261705158725764243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10908753507803439150509495 16363130261705158725764243)
        ·
          refine ⟨24544695392557738088646365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16363130261705158725764243 24544695392557738088646365)
          ·
            refine ⟨9204260772209151783242387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24544695392557738088646365 9204260772209151783242387)
            ·
              refine ⟨13806391158313727674863581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204260772209151783242387 13806391158313727674863581)
              ·
                refine ⟨5177396684367647878073843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13806391158313727674863581 5177396684367647878073843)
                ·
                  refine ⟨7766095026551471817110765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177396684367647878073843 7766095026551471817110765)
                  ·
                    refine ⟨2912285634956801931416537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7766095026551471817110765 2912285634956801931416537)
                    ·
                      refine ⟨2184214226217601448562403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912285634956801931416537 2184214226217601448562403)
                      ·
                        rfl

theorem cell23_4253742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4253742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253742 prefixEnd_4253742 := by exact prefixLift 4253742
  have htrace : WordTrace (prefixWord ++ tailWord_4253742) baseStart_4253742 baseEnd_4253742 := by
    simpa [prefixWord, tailWord_4253742, baseEnd_4253742] using wordTrace_append hprefix tailTrace_4253742
  have hstable : (prefixWord ++ tailWord_4253742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253742).length < 2 ^ (prefixWord ++ tailWord_4253742).sum := by decide
  have hdescent : baseEnd_4253742 < baseStart_4253742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253751 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_4253751 : Nat := 118140960795 + 4253751 * 2 ^ 59
def prefixEnd_4253751 : Nat := 4983230072969 + 3 ^ 40 * 4253751 * 2
def baseEnd_4253751 : Nat := 2184218847543491913349861

theorem tailTrace_4253751 : CollatzResearch.WordTrace tailWord_4253751 prefixEnd_4253751 2184218847543491913349861 := by
  unfold tailWord_4253751
  simp only [CollatzResearch.WordTrace]
  refine ⟨155147044812394084677657107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103431363208262723118438071 155147044812394084677657107)
  ·
    refine ⟨232720567218591127016485661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155147044812394084677657107 232720567218591127016485661)
    ·
      refine ⟨87270212706971672631182123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232720567218591127016485661 87270212706971672631182123)
      ·
        refine ⟨130905319060457508946773185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87270212706971672631182123 130905319060457508946773185)
        ·
          refine ⟨98178989295343131710079889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130905319060457508946773185 98178989295343131710079889)
          ·
            refine ⟨73634241971507348782559917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98178989295343131710079889 73634241971507348782559917)
            ·
              refine ⟨27612840739315255793459969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73634241971507348782559917 27612840739315255793459969)
              ·
                refine ⟨20709630554486441845094977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27612840739315255793459969 20709630554486441845094977)
                ·
                  refine ⟨15532222915864831383821233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20709630554486441845094977 15532222915864831383821233)
                  ·
                    refine ⟨11649167186898623537865925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15532222915864831383821233 11649167186898623537865925)
                    ·
                      refine ⟨2184218847543491913349861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11649167186898623537865925 2184218847543491913349861)
                      ·
                        rfl

theorem cell23_4253751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_4253751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253751 prefixEnd_4253751 := by exact prefixLift 4253751
  have htrace : WordTrace (prefixWord ++ tailWord_4253751) baseStart_4253751 baseEnd_4253751 := by
    simpa [prefixWord, tailWord_4253751, baseEnd_4253751] using wordTrace_append hprefix tailTrace_4253751
  have hstable : (prefixWord ++ tailWord_4253751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253751).length < 2 ^ (prefixWord ++ tailWord_4253751).sum := by decide
  have hdescent : baseEnd_4253751 < baseStart_4253751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253801 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_4253801 : Nat := 118140960795 + 4253801 * 2 ^ 59
def prefixEnd_4253801 : Nat := 4983230072969 + 3 ^ 40 * 4253801 * 2
def baseEnd_4253801 : Nat := 2184244521576216717724631

theorem tailTrace_4253801 : CollatzResearch.WordTrace tailWord_4253801 prefixEnd_4253801 2184244521576216717724631 := by
  unfold tailWord_4253801
  simp only [CollatzResearch.WordTrace]
  refine ⟨155148868462212943216977257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103432578974808628811318171 155148868462212943216977257)
  ·
    refine ⟨116361651346659707412732943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155148868462212943216977257 116361651346659707412732943)
    ·
      refine ⟨174542477019989561119099415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116361651346659707412732943 174542477019989561119099415)
      ·
        refine ⟨261813715529984341678649123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174542477019989561119099415 261813715529984341678649123)
        ·
          refine ⟨392720573294976512517973685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261813715529984341678649123 392720573294976512517973685)
          ·
            refine ⟨36817553746404048048560033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 392720573294976512517973685 36817553746404048048560033)
            ·
              refine ⟨27613165309803036036420025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36817553746404048048560033 27613165309803036036420025)
              ·
                refine ⟨20709873982352277027315019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27613165309803036036420025 20709873982352277027315019)
                ·
                  refine ⟨31064810973528415540972529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20709873982352277027315019 31064810973528415540972529)
                  ·
                    refine ⟨23298608230146311655729397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31064810973528415540972529 23298608230146311655729397)
                    ·
                      refine ⟨2184244521576216717724631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23298608230146311655729397 2184244521576216717724631)
                      ·
                        rfl

theorem cell23_4253801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_4253801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253801 prefixEnd_4253801 := by exact prefixLift 4253801
  have htrace : WordTrace (prefixWord ++ tailWord_4253801) baseStart_4253801 baseEnd_4253801 := by
    simpa [prefixWord, tailWord_4253801, baseEnd_4253801] using wordTrace_append hprefix tailTrace_4253801
  have hstable : (prefixWord ++ tailWord_4253801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253801).length < 2 ^ (prefixWord ++ tailWord_4253801).sum := by decide
  have hdescent : baseEnd_4253801 < baseStart_4253801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253808 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_4253808 : Nat := 118140960795 + 4253808 * 2 ^ 59
def prefixEnd_4253808 : Nat := 4983230072969 + 3 ^ 40 * 4253808 * 2
def baseEnd_4253808 : Nat := 728082705313599396779033

theorem tailTrace_4253808 : CollatzResearch.WordTrace tailWord_4253808 prefixEnd_4253808 728082705313599396779033 := by
  unfold tailWord_4253808
  simp only [CollatzResearch.WordTrace]
  refine ⟨77574561886593791706241039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103432749182125055608321385 77574561886593791706241039)
  ·
    refine ⟨116361842829890687559361559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77574561886593791706241039 116361842829890687559361559)
    ·
      refine ⟨174542764244836031339042339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116361842829890687559361559 174542764244836031339042339)
      ·
        refine ⟨261814146367254047008563509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174542764244836031339042339 261814146367254047008563509)
        ·
          refine ⟨24545076221930066907052829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 261814146367254047008563509 24545076221930066907052829)
          ·
            refine ⟨9204403583223775090144811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24545076221930066907052829 9204403583223775090144811)
            ·
              refine ⟨13806605374835662635217217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204403583223775090144811 13806605374835662635217217)
              ·
                refine ⟨10354954031126746976412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13806605374835662635217217 10354954031126746976412913)
                ·
                  refine ⟨7766215523345060232309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10354954031126746976412913 7766215523345060232309685)
                  ·
                    refine ⟨728082705313599396779033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7766215523345060232309685 728082705313599396779033)
                    ·
                      rfl

theorem cell23_4253808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_4253808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253808 prefixEnd_4253808 := by exact prefixLift 4253808
  have htrace : WordTrace (prefixWord ++ tailWord_4253808) baseStart_4253808 baseEnd_4253808 := by
    simpa [prefixWord, tailWord_4253808, baseEnd_4253808] using wordTrace_append hprefix tailTrace_4253808
  have hstable : (prefixWord ++ tailWord_4253808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253808).length < 2 ^ (prefixWord ++ tailWord_4253808).sum := by decide
  have hdescent : baseEnd_4253808 < baseStart_4253808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253828 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4253828 : Nat := 118140960795 + 4253828 * 2 ^ 59
def prefixEnd_4253828 : Nat := 4983230072969 + 3 ^ 40 * 4253828 * 2
def baseEnd_4253828 : Nat := 2184258385553888112087007

theorem tailTrace_4253828 : CollatzResearch.WordTrace tailWord_4253828 prefixEnd_4253828 2184258385553888112087007 := by
  unfold tailWord_4253828
  simp only [CollatzResearch.WordTrace]
  refine ⟨77574926616557563414105069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103433235488743417885473425 77574926616557563414105069)
  ·
    refine ⟨29090597481209086280289401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77574926616557563414105069 29090597481209086280289401)
    ·
      refine ⟨21817948110906814710217051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29090597481209086280289401 21817948110906814710217051)
      ·
        refine ⟨32726922166360222065325577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21817948110906814710217051 32726922166360222065325577)
        ·
          refine ⟨24545191624770166548994183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32726922166360222065325577 24545191624770166548994183)
          ·
            refine ⟨36817787437155249823491275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24545191624770166548994183 36817787437155249823491275)
            ·
              refine ⟨55226681155732874735236913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36817787437155249823491275 55226681155732874735236913)
              ·
                refine ⟨41420010866799656051427685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55226681155732874735236913 41420010866799656051427685)
                ·
                  refine ⟨7766252037524935509642691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41420010866799656051427685 7766252037524935509642691)
                  ·
                    refine ⟨11649378056287403264464037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7766252037524935509642691 11649378056287403264464037)
                    ·
                      refine ⟨2184258385553888112087007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11649378056287403264464037 2184258385553888112087007)
                      ·
                        rfl

theorem cell23_4253828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4253828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253828 prefixEnd_4253828 := by exact prefixLift 4253828
  have htrace : WordTrace (prefixWord ++ tailWord_4253828) baseStart_4253828 baseEnd_4253828 := by
    simpa [prefixWord, tailWord_4253828, baseEnd_4253828] using wordTrace_append hprefix tailTrace_4253828
  have hstable : (prefixWord ++ tailWord_4253828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253828).length < 2 ^ (prefixWord ++ tailWord_4253828).sum := by decide
  have hdescent : baseEnd_4253828 < baseStart_4253828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253871 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_4253871 : Nat := 118140960795 + 4253871 * 2 ^ 59
def prefixEnd_4253871 : Nat := 4983230072969 + 3 ^ 40 * 4253871 * 2
def baseEnd_4253871 : Nat := 2184280465222031443849309

theorem tailTrace_4253871 : CollatzResearch.WordTrace tailWord_4253871 prefixEnd_4253871 2184280465222031443849309 := by
  unfold tailWord_4253871
  simp only [CollatzResearch.WordTrace]
  refine ⟨155151421571959345172025467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103434281047972896781350311 155151421571959345172025467)
  ·
    refine ⟨232727132357939017758038201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155151421571959345172025467 232727132357939017758038201)
    ·
      refine ⟨174545349268454263318528651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232727132357939017758038201 174545349268454263318528651)
      ·
        refine ⟨261818023902681394977792977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174545349268454263318528651 261818023902681394977792977)
        ·
          refine ⟨196363517927011046233344733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261818023902681394977792977 196363517927011046233344733)
          ·
            refine ⟨73636319222629142337504275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196363517927011046233344733 73636319222629142337504275)
            ·
              refine ⟨110454478833943713506256413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73636319222629142337504275 110454478833943713506256413)
              ·
                refine ⟨41420429562728892564846155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110454478833943713506256413 41420429562728892564846155)
                ·
                  refine ⟨62130644344093338847269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41420429562728892564846155 62130644344093338847269233)
                  ·
                    refine ⟨46597983258070004135451925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62130644344093338847269233 46597983258070004135451925)
                    ·
                      refine ⟨2184280465222031443849309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46597983258070004135451925 2184280465222031443849309)
                      ·
                        rfl

theorem cell23_4253871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_4253871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253871 prefixEnd_4253871 := by exact prefixLift 4253871
  have htrace : WordTrace (prefixWord ++ tailWord_4253871) baseStart_4253871 baseEnd_4253871 := by
    simpa [prefixWord, tailWord_4253871, baseEnd_4253871] using wordTrace_append hprefix tailTrace_4253871
  have hstable : (prefixWord ++ tailWord_4253871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253871).length < 2 ^ (prefixWord ++ tailWord_4253871).sum := by decide
  have hdescent : baseEnd_4253871 < baseStart_4253871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253891 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_4253891 : Nat := 118140960795 + 4253891 * 2 ^ 59
def prefixEnd_4253891 : Nat := 4983230072969 + 3 ^ 40 * 4253891 * 2
def baseEnd_4253891 : Nat := 2184290734835121365599217

theorem tailTrace_4253891 : CollatzResearch.WordTrace tailWord_4253891 prefixEnd_4253891 2184290734835121365599217 := by
  unfold tailWord_4253891
  simp only [CollatzResearch.WordTrace]
  refine ⟨155152151031886888587753527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103434767354591259058502351 155152151031886888587753527)
  ·
    refine ⟨232728226547830332881630291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155152151031886888587753527 232728226547830332881630291)
    ·
      refine ⟨349092339821745499322445437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232728226547830332881630291 349092339821745499322445437)
      ·
        refine ⟨130909627433154562245917039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349092339821745499322445437 130909627433154562245917039)
        ·
          refine ⟨196364441149731843368875559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130909627433154562245917039 196364441149731843368875559)
          ·
            refine ⟨294546661724597765053313339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196364441149731843368875559 294546661724597765053313339)
            ·
              refine ⟨441819992586896647579970009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294546661724597765053313339 441819992586896647579970009)
              ·
                refine ⟨331364994440172485684977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441819992586896647579970009 331364994440172485684977507)
                ·
                  refine ⟨497047491660258728527466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331364994440172485684977507 497047491660258728527466261)
                  ·
                    refine ⟨23299101171574627899724981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 497047491660258728527466261 23299101171574627899724981)
                    ·
                      refine ⟨2184290734835121365599217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23299101171574627899724981 2184290734835121365599217)
                      ·
                        rfl

theorem cell23_4253891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_4253891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253891 prefixEnd_4253891 := by exact prefixLift 4253891
  have htrace : WordTrace (prefixWord ++ tailWord_4253891) baseStart_4253891 baseEnd_4253891 := by
    simpa [prefixWord, tailWord_4253891, baseEnd_4253891] using wordTrace_append hprefix tailTrace_4253891
  have hstable : (prefixWord ++ tailWord_4253891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253891).length < 2 ^ (prefixWord ++ tailWord_4253891).sum := by decide
  have hdescent : baseEnd_4253891 < baseStart_4253891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253898 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_4253898 : Nat := 118140960795 + 4253898 * 2 ^ 59
def prefixEnd_4253898 : Nat := 4983230072969 + 3 ^ 40 * 4253898 * 2
def baseEnd_4253898 : Nat := 728098109733234279403895

theorem tailTrace_4253898 : CollatzResearch.WordTrace tailWord_4253898 prefixEnd_4253898 728098109733234279403895 := by
  unfold tailWord_4253898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38788101585715382195814587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103434937561907685855505565 38788101585715382195814587)
  ·
    refine ⟨58182152378573073293721881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38788101585715382195814587 58182152378573073293721881)
    ·
      refine ⟨43636614283929804970291411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58182152378573073293721881 43636614283929804970291411)
      ·
        refine ⟨65454921425894707455437117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43636614283929804970291411 65454921425894707455437117)
        ·
          refine ⟨24545595534710515295788919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65454921425894707455437117 24545595534710515295788919)
          ·
            refine ⟨36818393302065772943683379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24545595534710515295788919 36818393302065772943683379)
            ·
              refine ⟨55227589953098659415525069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36818393302065772943683379 55227589953098659415525069)
              ·
                refine ⟨20710346232411997280821901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55227589953098659415525069 20710346232411997280821901)
                ·
                  refine ⟨7766379837154498980308213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20710346232411997280821901 7766379837154498980308213)
                  ·
                    refine ⟨728098109733234279403895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7766379837154498980308213 728098109733234279403895)
                    ·
                      rfl

theorem cell23_4253898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_4253898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253898 prefixEnd_4253898 := by exact prefixLift 4253898
  have htrace : WordTrace (prefixWord ++ tailWord_4253898) baseStart_4253898 baseEnd_4253898 := by
    simpa [prefixWord, tailWord_4253898, baseEnd_4253898] using wordTrace_append hprefix tailTrace_4253898
  have hstable : (prefixWord ++ tailWord_4253898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253898).length < 2 ^ (prefixWord ++ tailWord_4253898).sum := by decide
  have hdescent : baseEnd_4253898 < baseStart_4253898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253952 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2]
def baseStart_4253952 : Nat := 118140960795 + 4253952 * 2 ^ 59
def prefixEnd_4253952 : Nat := 4983230072969 + 3 ^ 40 * 4253952 * 2
def baseEnd_4253952 : Nat := 2184322057155045626936437

theorem tailTrace_4253952 : CollatzResearch.WordTrace tailWord_4253952 prefixEnd_4253952 2184322057155045626936437 := by
  unfold tailWord_4253952
  simp only [CollatzResearch.WordTrace]
  refine ⟨77577187942332948002862055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103436250589777264003816073 77577187942332948002862055)
  ·
    refine ⟨116365781913499422004293083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77577187942332948002862055 116365781913499422004293083)
    ·
      refine ⟨174548672870249133006439625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116365781913499422004293083 174548672870249133006439625)
      ·
        refine ⟨130911504652686849754829719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174548672870249133006439625 130911504652686849754829719)
        ·
          refine ⟨196367256979030274632244579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130911504652686849754829719 196367256979030274632244579)
          ·
            refine ⟨294550885468545411948366869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196367256979030274632244579 294550885468545411948366869)
            ·
              refine ⟨13807072756338066185079697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 294550885468545411948366869 13807072756338066185079697)
              ·
                refine ⟨10355304567253549638809773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13807072756338066185079697 10355304567253549638809773)
                ·
                  refine ⟨3883239212720081114553665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10355304567253549638809773 3883239212720081114553665)
                  ·
                    refine ⟨2912429409540060835915249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883239212720081114553665 2912429409540060835915249)
                    ·
                      refine ⟨2184322057155045626936437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912429409540060835915249 2184322057155045626936437)
                      ·
                        rfl

theorem cell23_4253952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_4253952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253952 prefixEnd_4253952 := by exact prefixLift 4253952
  have htrace : WordTrace (prefixWord ++ tailWord_4253952) baseStart_4253952 baseEnd_4253952 := by
    simpa [prefixWord, tailWord_4253952, baseEnd_4253952] using wordTrace_append hprefix tailTrace_4253952
  have hstable : (prefixWord ++ tailWord_4253952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253952).length < 2 ^ (prefixWord ++ tailWord_4253952).sum := by decide
  have hdescent : baseEnd_4253952 < baseStart_4253952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253982 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4253982 : Nat := 118140960795 + 4253982 * 2 ^ 59
def prefixEnd_4253982 : Nat := 4983230072969 + 3 ^ 40 * 4253982 * 2
def baseEnd_4253982 : Nat := 2184337461574680509561299

theorem tailTrace_4253982 : CollatzResearch.WordTrace tailWord_4253982 prefixEnd_4253982 2184337461574680509561299 := by
  unfold tailWord_4253982
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394433759319651391164525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103436980049704807419544133 19394433759319651391164525)
  ·
    refine ⟨7272912659744869271686697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19394433759319651391164525 7272912659744869271686697)
    ·
      refine ⟨5454684494808651953765023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7272912659744869271686697 5454684494808651953765023)
      ·
        refine ⟨8182026742212977930647535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454684494808651953765023 8182026742212977930647535)
        ·
          refine ⟨12273040113319466895971303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8182026742212977930647535 12273040113319466895971303)
          ·
            refine ⟨18409560169979200343956955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12273040113319466895971303 18409560169979200343956955)
            ·
              refine ⟨27614340254968800515935433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18409560169979200343956955 27614340254968800515935433)
              ·
                refine ⟨20710755191226600386951575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27614340254968800515935433 20710755191226600386951575)
                ·
                  refine ⟨31066132786839900580427363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20710755191226600386951575 31066132786839900580427363)
                  ·
                    refine ⟨46599199180259850870641045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31066132786839900580427363 46599199180259850870641045)
                    ·
                      refine ⟨2184337461574680509561299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46599199180259850870641045 2184337461574680509561299)
                      ·
                        rfl

theorem cell23_4253982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4253982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253982 prefixEnd_4253982 := by exact prefixLift 4253982
  have htrace : WordTrace (prefixWord ++ tailWord_4253982) baseStart_4253982 baseEnd_4253982 := by
    simpa [prefixWord, tailWord_4253982, baseEnd_4253982] using wordTrace_append hprefix tailTrace_4253982
  have hstable : (prefixWord ++ tailWord_4253982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253982).length < 2 ^ (prefixWord ++ tailWord_4253982).sum := by decide
  have hdescent : baseEnd_4253982 < baseStart_4253982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4253986 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4253986 : Nat := 118140960795 + 4253986 * 2 ^ 59
def prefixEnd_4253986 : Nat := 4983230072969 + 3 ^ 40 * 4253986 * 2
def baseEnd_4253986 : Nat := 2184339515497298493911281

theorem tailTrace_4253986 : CollatzResearch.WordTrace tailWord_4253986 prefixEnd_4253986 2184339515497298493911281 := by
  unfold tailWord_4253986
  simp only [CollatzResearch.WordTrace]
  refine ⟨38788903991635679953115453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103437077311028479874974541 38788903991635679953115453)
  ·
    refine ⟨14545838996863379982418295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38788903991635679953115453 14545838996863379982418295)
    ·
      refine ⟨21818758495295069973627443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14545838996863379982418295 21818758495295069973627443)
      ·
        refine ⟨32728137742942604960441165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21818758495295069973627443 32728137742942604960441165)
        ·
          refine ⟨12273051653603476860165437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32728137742942604960441165 12273051653603476860165437)
          ·
            refine ⟨4602394370101303822562039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12273051653603476860165437 4602394370101303822562039)
            ·
              refine ⟨6903591555151955733843059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602394370101303822562039 6903591555151955733843059)
              ·
                refine ⟨10355387332727933600764589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6903591555151955733843059 10355387332727933600764589)
                ·
                  refine ⟨3883270249772975100286721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10355387332727933600764589 3883270249772975100286721)
                  ·
                    refine ⟨2912452687329731325215041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883270249772975100286721 2912452687329731325215041)
                    ·
                      refine ⟨2184339515497298493911281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912452687329731325215041 2184339515497298493911281)
                      ·
                        rfl

theorem cell23_4253986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4253986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4253986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4253986 prefixEnd_4253986 := by exact prefixLift 4253986
  have htrace : WordTrace (prefixWord ++ tailWord_4253986) baseStart_4253986 baseEnd_4253986 := by
    simpa [prefixWord, tailWord_4253986, baseEnd_4253986] using wordTrace_append hprefix tailTrace_4253986
  have hstable : (prefixWord ++ tailWord_4253986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4253986).length < 2 ^ (prefixWord ++ tailWord_4253986).sum := by decide
  have hdescent : baseEnd_4253986 < baseStart_4253986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4253986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254012 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_4254012 : Nat := 118140960795 + 4254012 * 2 ^ 59
def prefixEnd_4254012 : Nat := 4983230072969 + 3 ^ 40 * 4254012 * 2
def baseEnd_4254012 : Nat := 2184352865994315392186161

theorem tailTrace_4254012 : CollatzResearch.WordTrace tailWord_4254012 prefixEnd_4254012 2184352865994315392186161 := by
  unfold tailWord_4254012
  simp only [CollatzResearch.WordTrace]
  refine ⟨77578282132224263126454145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103437709509632350835272193 77578282132224263126454145)
  ·
    refine ⟨58183711599168197344840609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77578282132224263126454145 58183711599168197344840609)
    ·
      refine ⟨43637783699376148008630457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58183711599168197344840609 43637783699376148008630457)
      ·
        refine ⟨32728337774532111006472843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43637783699376148008630457 32728337774532111006472843)
        ·
          refine ⟨49092506661798166509709265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32728337774532111006472843 49092506661798166509709265)
          ·
            refine ⟨36819379996348624882281949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49092506661798166509709265 36819379996348624882281949)
            ·
              refine ⟨13807267498630734330855731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36819379996348624882281949 13807267498630734330855731)
              ·
                refine ⟨20710901247946101496283597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13807267498630734330855731 20710901247946101496283597)
                ·
                  refine ⟨7766587967979788061106349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20710901247946101496283597 7766587967979788061106349)
                  ·
                    refine ⟨2912470487992420522914881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7766587967979788061106349 2912470487992420522914881)
                    ·
                      refine ⟨2184352865994315392186161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912470487992420522914881 2184352865994315392186161)
                      ·
                        rfl

theorem cell23_4254012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_4254012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254012 prefixEnd_4254012 := by exact prefixLift 4254012
  have htrace : WordTrace (prefixWord ++ tailWord_4254012) baseStart_4254012 baseEnd_4254012 := by
    simpa [prefixWord, tailWord_4254012, baseEnd_4254012] using wordTrace_append hprefix tailTrace_4254012
  have hstable : (prefixWord ++ tailWord_4254012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254012).length < 2 ^ (prefixWord ++ tailWord_4254012).sum := by decide
  have hdescent : baseEnd_4254012 < baseStart_4254012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254055 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4254055 : Nat := 118140960795 + 4254055 * 2 ^ 59
def prefixEnd_4254055 : Nat := 4983230072969 + 3 ^ 40 * 4254055 * 2
def baseEnd_4254055 : Nat := 2184374945662458723948463

theorem tailTrace_4254055 : CollatzResearch.WordTrace tailWord_4254055 prefixEnd_4254055 2184374945662458723948463 := by
  unfold tailWord_4254055
  simp only [CollatzResearch.WordTrace]
  refine ⟨155158132603292744596723619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103438755068861829731149079 155158132603292744596723619)
  ·
    refine ⟨232737198904939116895085429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155158132603292744596723619 232737198904939116895085429)
    ·
      refine ⟨21819112397338042208914259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232737198904939116895085429 21819112397338042208914259)
      ·
        refine ⟨32728668596007063313371389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21819112397338042208914259 32728668596007063313371389)
        ·
          refine ⟨12273250723502648742514271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32728668596007063313371389 12273250723502648742514271)
          ·
            refine ⟨18409876085253973113771407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12273250723502648742514271 18409876085253973113771407)
            ·
              refine ⟨27614814127880959670657111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18409876085253973113771407 27614814127880959670657111)
              ·
                refine ⟨41422221191821439505985667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27614814127880959670657111 41422221191821439505985667)
                ·
                  refine ⟨62133331787732159258978501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41422221191821439505985667 62133331787732159258978501)
                  ·
                    refine ⟨11649999710199779861058469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62133331787732159258978501 11649999710199779861058469)
                    ·
                      refine ⟨2184374945662458723948463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11649999710199779861058469 2184374945662458723948463)
                      ·
                        rfl

theorem cell23_4254055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4254055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254055 prefixEnd_4254055 := by exact prefixLift 4254055
  have htrace : WordTrace (prefixWord ++ tailWord_4254055) baseStart_4254055 baseEnd_4254055 := by
    simpa [prefixWord, tailWord_4254055, baseEnd_4254055] using wordTrace_append hprefix tailTrace_4254055
  have hstable : (prefixWord ++ tailWord_4254055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254055).length < 2 ^ (prefixWord ++ tailWord_4254055).sum := by decide
  have hdescent : baseEnd_4254055 < baseStart_4254055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254110 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4254110 : Nat := 118140960795 + 4254110 * 2 ^ 59
def prefixEnd_4254110 : Nat := 4983230072969 + 3 ^ 40 * 4254110 * 2
def baseEnd_4254110 : Nat := 2184403187098456008760711

theorem tailTrace_4254110 : CollatzResearch.WordTrace tailWord_4254110 prefixEnd_4254110 2184403187098456008760711 := by
  unfold tailWord_4254110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395017327261686123746973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103440092412062325993317189 19395017327261686123746973)
  ·
    refine ⟨7273131497723132296405115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19395017327261686123746973 7273131497723132296405115)
    ·
      refine ⟨10909697246584698444607673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7273131497723132296405115 10909697246584698444607673)
      ·
        refine ⟨8182272934938523833455755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10909697246584698444607673 8182272934938523833455755)
        ·
          refine ⟨12273409402407785750183633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8182272934938523833455755 12273409402407785750183633)
          ·
            refine ⟨9205057051805839312637725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12273409402407785750183633 9205057051805839312637725)
            ·
              refine ⟨3451896394427189742239147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9205057051805839312637725 3451896394427189742239147)
              ·
                refine ⟨5177844591640784613358721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451896394427189742239147 5177844591640784613358721)
                ·
                  refine ⟨3883383443730588460019041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5177844591640784613358721 3883383443730588460019041)
                  ·
                    refine ⟨2912537582797941345014281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883383443730588460019041 2912537582797941345014281)
                    ·
                      refine ⟨2184403187098456008760711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912537582797941345014281 2184403187098456008760711)
                      ·
                        rfl

theorem cell23_4254110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4254110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254110 prefixEnd_4254110 := by exact prefixLift 4254110
  have htrace : WordTrace (prefixWord ++ tailWord_4254110) baseStart_4254110 baseEnd_4254110 := by
    simpa [prefixWord, tailWord_4254110, baseEnd_4254110] using wordTrace_append hprefix tailTrace_4254110
  have hstable : (prefixWord ++ tailWord_4254110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254110).length < 2 ^ (prefixWord ++ tailWord_4254110).sum := by decide
  have hdescent : baseEnd_4254110 < baseStart_4254110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254115 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_4254115 : Nat := 118140960795 + 4254115 * 2 ^ 59
def prefixEnd_4254115 : Nat := 4983230072969 + 3 ^ 40 * 4254115 * 2
def baseEnd_4254115 : Nat := 2184405754501728489198187

theorem tailTrace_4254115 : CollatzResearch.WordTrace tailWord_4254115 prefixEnd_4254115 2184405754501728489198187 := by
  unfold tailWord_4254115
  simp only [CollatzResearch.WordTrace]
  refine ⟨155160320983075374843907799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103440213988716916562605199 155160320983075374843907799)
  ·
    refine ⟨232740481474613062265861699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155160320983075374843907799 232740481474613062265861699)
    ·
      refine ⟨349110722211919593398792549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232740481474613062265861699 349110722211919593398792549)
      ·
        refine ⟨65458260414734923762273603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 349110722211919593398792549 65458260414734923762273603)
        ·
          refine ⟨98187390622102385643410405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65458260414734923762273603 98187390622102385643410405)
          ·
            refine ⟨18410135741644197308139451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98187390622102385643410405 18410135741644197308139451)
            ·
              refine ⟨27615203612466295962209177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18410135741644197308139451 27615203612466295962209177)
              ·
                refine ⟨20711402709349721971656883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27615203612466295962209177 20711402709349721971656883)
                ·
                  refine ⟨31067104064024582957485325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20711402709349721971656883 31067104064024582957485325)
                  ·
                    refine ⟨11650164024009218609056997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31067104064024582957485325 11650164024009218609056997)
                    ·
                      refine ⟨2184405754501728489198187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11650164024009218609056997 2184405754501728489198187)
                      ·
                        rfl

theorem cell23_4254115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_4254115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254115 prefixEnd_4254115 := by exact prefixLift 4254115
  have htrace : WordTrace (prefixWord ++ tailWord_4254115) baseStart_4254115 baseEnd_4254115 := by
    simpa [prefixWord, tailWord_4254115, baseEnd_4254115] using wordTrace_append hprefix tailTrace_4254115
  have hstable : (prefixWord ++ tailWord_4254115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254115).length < 2 ^ (prefixWord ++ tailWord_4254115).sum := by decide
  have hdescent : baseEnd_4254115 < baseStart_4254115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254142 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_4254142 : Nat := 118140960795 + 4254142 * 2 ^ 59
def prefixEnd_4254142 : Nat := 4983230072969 + 3 ^ 40 * 4254142 * 2
def baseEnd_4254142 : Nat := 728139872826466627853521

theorem tailTrace_4254142 : CollatzResearch.WordTrace tailWord_4254142 prefixEnd_4254142 728139872826466627853521 := by
  unfold tailWord_4254142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395163219247194806892585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103440870502651705636760453 19395163219247194806892585)
  ·
    refine ⟨14546372414435396105169439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19395163219247194806892585 14546372414435396105169439)
    ·
      refine ⟨21819558621653094157754159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14546372414435396105169439 21819558621653094157754159)
      ·
        refine ⟨32729337932479641236631239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21819558621653094157754159 32729337932479641236631239)
        ·
          refine ⟨49094006898719461854946859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32729337932479641236631239 49094006898719461854946859)
          ·
            refine ⟨73641010348079192782420289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49094006898719461854946859 73641010348079192782420289)
            ·
              refine ⟨55230757761059394586815217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73641010348079192782420289 55230757761059394586815217)
              ·
                refine ⟨41423068320794545940111413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55230757761059394586815217 41423068320794545940111413)
                ·
                  refine ⟨3883412655074488681885445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41423068320794545940111413 3883412655074488681885445)
                  ·
                    refine ⟨728139872826466627853521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883412655074488681885445 728139872826466627853521)
                    ·
                      rfl

theorem cell23_4254142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_4254142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254142 prefixEnd_4254142 := by exact prefixLift 4254142
  have htrace : WordTrace (prefixWord ++ tailWord_4254142) baseStart_4254142 baseEnd_4254142 := by
    simpa [prefixWord, tailWord_4254142, baseEnd_4254142] using wordTrace_append hprefix tailTrace_4254142
  have hstable : (prefixWord ++ tailWord_4254142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254142).length < 2 ^ (prefixWord ++ tailWord_4254142).sum := by decide
  have hdescent : baseEnd_4254142 < baseStart_4254142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254152 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_4254152 : Nat := 118140960795 + 4254152 * 2 ^ 59
def prefixEnd_4254152 : Nat := 4983230072969 + 3 ^ 40 * 4254152 * 2
def baseEnd_4254152 : Nat := 2184424753285944844435517

theorem tailTrace_4254152 : CollatzResearch.WordTrace tailWord_4254152 prefixEnd_4254152 2184424753285944844435517 := by
  unfold tailWord_4254152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77580835241970665081502355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103441113655960886775336473 77580835241970665081502355)
  ·
    refine ⟨116371252862955997622253533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77580835241970665081502355 116371252862955997622253533)
    ·
      refine ⟨43639219823608499108345075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116371252862955997622253533 43639219823608499108345075)
      ·
        refine ⟨65458829735412748662517613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43639219823608499108345075 65458829735412748662517613)
        ·
          refine ⟨24547061150779780748444105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65458829735412748662517613 24547061150779780748444105)
          ·
            refine ⟨18410295863084835561333079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24547061150779780748444105 18410295863084835561333079)
            ·
              refine ⟨27615443794627253341999619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18410295863084835561333079 27615443794627253341999619)
              ·
                refine ⟨41423165691940880012999429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27615443794627253341999619 41423165691940880012999429)
                ·
                  refine ⟨7766843567238915002437393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41423165691940880012999429 7766843567238915002437393)
                  ·
                    refine ⟨5825132675429186251828045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7766843567238915002437393 5825132675429186251828045)
                    ·
                      refine ⟨2184424753285944844435517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825132675429186251828045 2184424753285944844435517)
                      ·
                        rfl

theorem cell23_4254152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_4254152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254152 prefixEnd_4254152 := by exact prefixLift 4254152
  have htrace : WordTrace (prefixWord ++ tailWord_4254152) baseStart_4254152 baseEnd_4254152 := by
    simpa [prefixWord, tailWord_4254152, baseEnd_4254152] using wordTrace_append hprefix tailTrace_4254152
  have hstable : (prefixWord ++ tailWord_4254152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254152).length < 2 ^ (prefixWord ++ tailWord_4254152).sum := by decide
  have hdescent : baseEnd_4254152 < baseStart_4254152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254155 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 6]
def baseStart_4254155 : Nat := 118140960795 + 4254155 * 2 ^ 59
def prefixEnd_4254155 : Nat := 4983230072969 + 3 ^ 40 * 4254155 * 2
def baseEnd_4254155 : Nat := 242714032636434259188667

theorem tailTrace_4254155 : CollatzResearch.WordTrace tailWord_4254155 prefixEnd_4254155 242714032636434259188667 := by
  unfold tailWord_4254155
  simp only [CollatzResearch.WordTrace]
  refine ⟨155161779902930461675363919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103441186601953641116909279 155161779902930461675363919)
  ·
    refine ⟨232742669854395692513045879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155161779902930461675363919 232742669854395692513045879)
    ·
      refine ⟨349114004781593538769568819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232742669854395692513045879 349114004781593538769568819)
      ·
        refine ⟨523671007172390308154353229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349114004781593538769568819 523671007172390308154353229)
        ·
          refine ⟨196376627689646365557882461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523671007172390308154353229 196376627689646365557882461)
          ·
            refine ⟨73641235383617387084205923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196376627689646365557882461 73641235383617387084205923)
            ·
              refine ⟨110461853075426080626308885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73641235383617387084205923 110461853075426080626308885)
              ·
                refine ⟨5177899362910597529358229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110461853075426080626308885 5177899362910597529358229)
                ·
                  refine ⟨242714032636434259188667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5177899362910597529358229 242714032636434259188667)
                  ·
                    rfl

theorem cell23_4254155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 6].length) (baseStart_4254155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254155 prefixEnd_4254155 := by exact prefixLift 4254155
  have htrace : WordTrace (prefixWord ++ tailWord_4254155) baseStart_4254155 baseEnd_4254155 := by
    simpa [prefixWord, tailWord_4254155, baseEnd_4254155] using wordTrace_append hprefix tailTrace_4254155
  have hstable : (prefixWord ++ tailWord_4254155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254155).length < 2 ^ (prefixWord ++ tailWord_4254155).sum := by decide
  have hdescent : baseEnd_4254155 < baseStart_4254155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254232 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_4254232 : Nat := 118140960795 + 4254232 * 2 ^ 59
def prefixEnd_4254232 : Nat := 4983230072969 + 3 ^ 40 * 4254232 * 2
def baseEnd_4254232 : Nat := 728155277246101510478383

theorem tailTrace_4254232 : CollatzResearch.WordTrace tailWord_4254232 prefixEnd_4254232 728155277246101510478383 := by
  unfold tailWord_4254232
  simp only [CollatzResearch.WordTrace]
  refine ⟨77582294161825751912958475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103443058882434335883944633 77582294161825751912958475)
  ·
    refine ⟨116373441242738627869437713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77582294161825751912958475 116373441242738627869437713)
    ·
      refine ⟨87280080932053970902078285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116373441242738627869437713 87280080932053970902078285)
      ·
        refine ⟨32730030349520239088279357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87280080932053970902078285 32730030349520239088279357)
        ·
          refine ⟨12273761381070089658104759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32730030349520239088279357 12273761381070089658104759)
          ·
            refine ⟨18410642071605134487157139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12273761381070089658104759 18410642071605134487157139)
            ·
              refine ⟨27615963107407701730735709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18410642071605134487157139 27615963107407701730735709)
              ·
                refine ⟨10355986165277888149025891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27615963107407701730735709 10355986165277888149025891)
                ·
                  refine ⟨15533979247916832223538837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10355986165277888149025891 15533979247916832223538837)
                  ·
                    refine ⟨728155277246101510478383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15533979247916832223538837 728155277246101510478383)
                    ·
                      rfl

theorem cell23_4254232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_4254232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254232 prefixEnd_4254232 := by exact prefixLift 4254232
  have htrace : WordTrace (prefixWord ++ tailWord_4254232) baseStart_4254232 baseEnd_4254232 := by
    simpa [prefixWord, tailWord_4254232, baseEnd_4254232] using wordTrace_append hprefix tailTrace_4254232
  have hstable : (prefixWord ++ tailWord_4254232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254232).length < 2 ^ (prefixWord ++ tailWord_4254232).sum := by decide
  have hdescent : baseEnd_4254232 < baseStart_4254232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254245 : List Nat := [1, 3, 1, 2, 2, 1, 2, 11]
def baseStart_4254245 : Nat := 118140960795 + 4254245 * 2 ^ 59
def prefixEnd_4254245 : Nat := 4983230072969 + 3 ^ 40 * 4254245 * 2
def baseEnd_4254245 : Nat := 80906389147659740021207

theorem tailTrace_4254245 : CollatzResearch.WordTrace tailWord_4254245 prefixEnd_4254245 80906389147659740021207 := by
  unfold tailWord_4254245
  simp only [CollatzResearch.WordTrace]
  refine ⟨155165062472604407046140189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103443374981736271364093459 155165062472604407046140189)
  ·
    refine ⟨58186898427226652642302571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155165062472604407046140189 58186898427226652642302571)
    ·
      refine ⟨87280347640839978963453857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58186898427226652642302571 87280347640839978963453857)
      ·
        refine ⟨65460260730629984222590393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87280347640839978963453857 65460260730629984222590393)
        ·
          refine ⟨49095195547972488166942795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65460260730629984222590393 49095195547972488166942795)
          ·
            refine ⟨73642793321958732250414193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49095195547972488166942795 73642793321958732250414193)
            ·
              refine ⟨55232094991469049187810645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73642793321958732250414193 55232094991469049187810645)
              ·
                refine ⟨80906389147659740021207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55232094991469049187810645 80906389147659740021207)
                ·
                  rfl

theorem cell23_4254245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 11].length) (baseStart_4254245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254245 prefixEnd_4254245 := by exact prefixLift 4254245
  have htrace : WordTrace (prefixWord ++ tailWord_4254245) baseStart_4254245 baseEnd_4254245 := by
    simpa [prefixWord, tailWord_4254245, baseEnd_4254245] using wordTrace_append hprefix tailTrace_4254245
  have hstable : (prefixWord ++ tailWord_4254245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254245).length < 2 ^ (prefixWord ++ tailWord_4254245).sum := by decide
  have hdescent : baseEnd_4254245 < baseStart_4254245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254259 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 3]
def baseStart_4254259 : Nat := 118140960795 + 4254259 * 2 ^ 59
def prefixEnd_4254259 : Nat := 4983230072969 + 3 ^ 40 * 4254259 * 2
def baseEnd_4254259 : Nat := 2184479695715975925797525

theorem tailTrace_4254259 : CollatzResearch.WordTrace tailWord_4254259 prefixEnd_4254259 2184479695715975925797525 := by
  unfold tailWord_4254259
  simp only [CollatzResearch.WordTrace]
  refine ⟨155165573094553687437149831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103443715396369124958099887 155165573094553687437149831)
  ·
    refine ⟨232748359641830531155724747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155165573094553687437149831 232748359641830531155724747)
    ·
      refine ⟨349122539462745796733587121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232748359641830531155724747 349122539462745796733587121)
      ·
        refine ⟨261841904597059347550190341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349122539462745796733587121 261841904597059347550190341)
        ·
          refine ⟨49095357111948627665660689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261841904597059347550190341 49095357111948627665660689)
          ·
            refine ⟨36821517833961470749245517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49095357111948627665660689 36821517833961470749245517)
            ·
              refine ⟨13808069187735551530967069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36821517833961470749245517 13808069187735551530967069)
              ·
                refine ⟨5178025945400831824112651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13808069187735551530967069 5178025945400831824112651)
                ·
                  refine ⟨7767038918101247736168977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178025945400831824112651 7767038918101247736168977)
                  ·
                    refine ⟨5825279188575935802126733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7767038918101247736168977 5825279188575935802126733)
                    ·
                      refine ⟨2184479695715975925797525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825279188575935802126733 2184479695715975925797525)
                      ·
                        rfl

theorem cell23_4254259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_4254259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254259 prefixEnd_4254259 := by exact prefixLift 4254259
  have htrace : WordTrace (prefixWord ++ tailWord_4254259) baseStart_4254259 baseEnd_4254259 := by
    simpa [prefixWord, tailWord_4254259, baseEnd_4254259] using wordTrace_append hprefix tailTrace_4254259
  have hstable : (prefixWord ++ tailWord_4254259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254259).length < 2 ^ (prefixWord ++ tailWord_4254259).sum := by decide
  have hdescent : baseEnd_4254259 < baseStart_4254259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254266 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_4254266 : Nat := 118140960795 + 4254266 * 2 ^ 59
def prefixEnd_4254266 : Nat := 4983230072969 + 3 ^ 40 * 4254266 * 2
def baseEnd_4254266 : Nat := 728161096693519132803331

theorem tailTrace_4254266 : CollatzResearch.WordTrace tailWord_4254266 prefixEnd_4254266 728161096693519132803331 := by
  unfold tailWord_4254266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38791457101382081908163663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103443885603685551755103101 38791457101382081908163663)
  ·
    refine ⟨58187185652073122862245495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38791457101382081908163663 58187185652073122862245495)
    ·
      refine ⟨87280778478109684293368243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58187185652073122862245495 87280778478109684293368243)
      ·
        refine ⟨130921167717164526440052365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87280778478109684293368243 130921167717164526440052365)
        ·
          refine ⟨49095437893936697415019637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130921167717164526440052365 49095437893936697415019637)
          ·
            refine ⟨4602697302556565382658091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49095437893936697415019637 4602697302556565382658091)
            ·
              refine ⟨6904045953834848073987137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602697302556565382658091 6904045953834848073987137)
              ·
                refine ⟨5178034465376136055490353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904045953834848073987137 5178034465376136055490353)
                ·
                  refine ⟨3883525849032102041617765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178034465376136055490353 3883525849032102041617765)
                  ·
                    refine ⟨728161096693519132803331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883525849032102041617765 728161096693519132803331)
                    ·
                      rfl

theorem cell23_4254266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_4254266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254266 prefixEnd_4254266 := by exact prefixLift 4254266
  have htrace : WordTrace (prefixWord ++ tailWord_4254266) baseStart_4254266 baseEnd_4254266 := by
    simpa [prefixWord, tailWord_4254266, baseEnd_4254266] using wordTrace_append hprefix tailTrace_4254266
  have hstable : (prefixWord ++ tailWord_4254266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254266).length < 2 ^ (prefixWord ++ tailWord_4254266).sum := by decide
  have hdescent : baseEnd_4254266 < baseStart_4254266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254272 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_4254272 : Nat := 118140960795 + 4254272 * 2 ^ 59
def prefixEnd_4254272 : Nat := 4983230072969 + 3 ^ 40 * 4254272 * 2
def baseEnd_4254272 : Nat := 2184486370964484374934965

theorem tailTrace_4254272 : CollatzResearch.WordTrace tailWord_4254272 prefixEnd_4254272 2184486370964484374934965 := by
  unfold tailWord_4254272
  simp only [CollatzResearch.WordTrace]
  refine ⟨77583023621753295328686535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103444031495671060438248713 77583023621753295328686535)
  ·
    refine ⟨116374535432629942993029803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77583023621753295328686535 116374535432629942993029803)
    ·
      refine ⟨174561803148944914489544705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116374535432629942993029803 174561803148944914489544705)
      ·
        refine ⟨130921352361708685867158529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174561803148944914489544705 130921352361708685867158529)
        ·
          refine ⟨98191014271281514400368897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130921352361708685867158529 98191014271281514400368897)
          ·
            refine ⟨73643260703461135800276673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98191014271281514400368897 73643260703461135800276673)
            ·
              refine ⟨55232445527595851850207505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73643260703461135800276673 55232445527595851850207505)
              ·
                refine ⟨41424334145696888887655629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55232445527595851850207505 41424334145696888887655629)
                ·
                  refine ⟨15534125304636333332870861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41424334145696888887655629 15534125304636333332870861)
                  ·
                    refine ⟨5825296989238624999826573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15534125304636333332870861 5825296989238624999826573)
                    ·
                      refine ⟨2184486370964484374934965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825296989238624999826573 2184486370964484374934965)
                      ·
                        rfl

theorem cell23_4254272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_4254272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254272 prefixEnd_4254272 := by exact prefixLift 4254272
  have htrace : WordTrace (prefixWord ++ tailWord_4254272) baseStart_4254272 baseEnd_4254272 := by
    simpa [prefixWord, tailWord_4254272, baseEnd_4254272] using wordTrace_append hprefix tailTrace_4254272
  have hstable : (prefixWord ++ tailWord_4254272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254272).length < 2 ^ (prefixWord ++ tailWord_4254272).sum := by decide
  have hdescent : baseEnd_4254272 < baseStart_4254272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254273 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4254273 : Nat := 118140960795 + 4254273 * 2 ^ 59
def prefixEnd_4254273 : Nat := 4983230072969 + 3 ^ 40 * 4254273 * 2
def baseEnd_4254273 : Nat := 2184486884445138871022461

theorem tailTrace_4254273 : CollatzResearch.WordTrace tailWord_4254273 prefixEnd_4254273 2184486884445138871022461 := by
  unfold tailWord_4254273
  simp only [CollatzResearch.WordTrace]
  refine ⟨155166083716502967828159473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103444055811001978552106315 155166083716502967828159473)
  ·
    refine ⟨116374562787377225871119605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155166083716502967828159473 116374562787377225871119605)
    ·
      refine ⟨10910115261316614925417463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116374562787377225871119605 10910115261316614925417463)
      ·
        refine ⟨16365172891974922388126195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10910115261316614925417463 16365172891974922388126195)
        ·
          refine ⟨24547759337962383582189293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16365172891974922388126195 24547759337962383582189293)
          ·
            refine ⟨9205409751735893843320985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24547759337962383582189293 9205409751735893843320985)
            ·
              refine ⟨6904057313801920382490739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9205409751735893843320985 6904057313801920382490739)
              ·
                refine ⟨10356085970702880573736109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904057313801920382490739 10356085970702880573736109)
                ·
                  refine ⟨3883532239013580215151041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10356085970702880573736109 3883532239013580215151041)
                  ·
                    refine ⟨2912649179260185161363281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883532239013580215151041 2912649179260185161363281)
                    ·
                      refine ⟨2184486884445138871022461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912649179260185161363281 2184486884445138871022461)
                      ·
                        rfl

theorem cell23_4254273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4254273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254273 prefixEnd_4254273 := by exact prefixLift 4254273
  have htrace : WordTrace (prefixWord ++ tailWord_4254273) baseStart_4254273 baseEnd_4254273 := by
    simpa [prefixWord, tailWord_4254273, baseEnd_4254273] using wordTrace_append hprefix tailTrace_4254273
  have hstable : (prefixWord ++ tailWord_4254273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254273).length < 2 ^ (prefixWord ++ tailWord_4254273).sum := by decide
  have hdescent : baseEnd_4254273 < baseStart_4254273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254275 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 9]
def baseStart_4254275 : Nat := 118140960795 + 4254275 * 2 ^ 59
def prefixEnd_4254275 : Nat := 4983230072969 + 3 ^ 40 * 4254275 * 2
def baseEnd_4254275 : Nat := 728162637135482621065817

theorem tailTrace_4254275 : CollatzResearch.WordTrace tailWord_4254275 prefixEnd_4254275 728162637135482621065817 := by
  unfold tailWord_4254275
  simp only [CollatzResearch.WordTrace]
  refine ⟨155166156662495722169732279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103444104441663814779821519 155166156662495722169732279)
  ·
    refine ⟨232749234993743583254598419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155166156662495722169732279 232749234993743583254598419)
    ·
      refine ⟨349123852490615374881897629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232749234993743583254598419 349123852490615374881897629)
      ·
        refine ⟨130921444683980765580711611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349123852490615374881897629 130921444683980765580711611)
        ·
          refine ⟨196382167025971148371067417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130921444683980765580711611 196382167025971148371067417)
          ·
            refine ⟨147286625269478361278300563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196382167025971148371067417 147286625269478361278300563)
            ·
              refine ⟨220929937904217541917450845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147286625269478361278300563 220929937904217541917450845)
              ·
                refine ⟨82848726714081578219044067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220929937904217541917450845 82848726714081578219044067)
                ·
                  refine ⟨124273090071122367328566101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82848726714081578219044067 124273090071122367328566101)
                  ·
                    refine ⟨728162637135482621065817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124273090071122367328566101 728162637135482621065817)
                    ·
                      rfl

theorem cell23_4254275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_4254275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254275 prefixEnd_4254275 := by exact prefixLift 4254275
  have htrace : WordTrace (prefixWord ++ tailWord_4254275) baseStart_4254275 baseEnd_4254275 := by
    simpa [prefixWord, tailWord_4254275, baseEnd_4254275] using wordTrace_append hprefix tailTrace_4254275
  have hstable : (prefixWord ++ tailWord_4254275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254275).length < 2 ^ (prefixWord ++ tailWord_4254275).sum := by decide
  have hdescent : baseEnd_4254275 < baseStart_4254275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254289 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_4254289 : Nat := 118140960795 + 4254289 * 2 ^ 59
def prefixEnd_4254289 : Nat := 4983230072969 + 3 ^ 40 * 4254289 * 2
def baseEnd_4254289 : Nat := 2184495100135610808422387

theorem tailTrace_4254289 : CollatzResearch.WordTrace tailWord_4254289 prefixEnd_4254289 2184495100135610808422387 := by
  unfold tailWord_4254289
  simp only [CollatzResearch.WordTrace]
  refine ⟨155166667284445002560741921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103444444856296668373827947 155166667284445002560741921)
  ·
    refine ⟨116375000463333751920556441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155166667284445002560741921 116375000463333751920556441)
    ·
      refine ⟨87281250347500313940417331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116375000463333751920556441 87281250347500313940417331)
      ·
        refine ⟨130921875521250470910625997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87281250347500313940417331 130921875521250470910625997)
        ·
          refine ⟨49095703320468926591484749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130921875521250470910625997 49095703320468926591484749)
          ·
            refine ⟨18410888745175847471806781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49095703320468926591484749 18410888745175847471806781)
            ·
              refine ⟨6904083279440942801927543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18410888745175847471806781 6904083279440942801927543)
              ·
                refine ⟨10356124919161414202891315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904083279440942801927543 10356124919161414202891315)
                ·
                  refine ⟨15534187378742121304336973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10356124919161414202891315 15534187378742121304336973)
                  ·
                    refine ⟨5825320267028295489126365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15534187378742121304336973 5825320267028295489126365)
                    ·
                      refine ⟨2184495100135610808422387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825320267028295489126365 2184495100135610808422387)
                      ·
                        rfl

theorem cell23_4254289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_4254289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254289 prefixEnd_4254289 := by exact prefixLift 4254289
  have htrace : WordTrace (prefixWord ++ tailWord_4254289) baseStart_4254289 baseEnd_4254289 := by
    simpa [prefixWord, tailWord_4254289, baseEnd_4254289] using wordTrace_append hprefix tailTrace_4254289
  have hstable : (prefixWord ++ tailWord_4254289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254289).length < 2 ^ (prefixWord ++ tailWord_4254289).sum := by decide
  have hdescent : baseEnd_4254289 < baseStart_4254289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254316 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_4254316 : Nat := 118140960795 + 4254316 * 2 ^ 59
def prefixEnd_4254316 : Nat := 4983230072969 + 3 ^ 40 * 4254316 * 2
def baseEnd_4254316 : Nat := 2184508964113282202784763

theorem tailTrace_4254316 : CollatzResearch.WordTrace tailWord_4254316 prefixEnd_4254316 2184508964113282202784763 := by
  unfold tailWord_4254316
  simp only [CollatzResearch.WordTrace]
  refine ⟨77583826027673593085987401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103445101370231457447983201 77583826027673593085987401)
  ·
    refine ⟨58187869520755194814490551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77583826027673593085987401 58187869520755194814490551)
    ·
      refine ⟨87281804281132792221735827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58187869520755194814490551 87281804281132792221735827)
      ·
        refine ⟨130922706421699188332603741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87281804281132792221735827 130922706421699188332603741)
        ·
          refine ⟨49096014908137195624726403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130922706421699188332603741 49096014908137195624726403)
          ·
            refine ⟨73644022362205793437089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49096014908137195624726403 73644022362205793437089605)
            ·
              refine ⟨13808254192913586269454301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73644022362205793437089605 13808254192913586269454301)
              ·
                refine ⟨5178095322342594851045363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13808254192913586269454301 5178095322342594851045363)
                ·
                  refine ⟨7767142983513892276568045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178095322342594851045363 7767142983513892276568045)
                  ·
                    refine ⟨2912678618817709603713017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7767142983513892276568045 2912678618817709603713017)
                    ·
                      refine ⟨2184508964113282202784763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912678618817709603713017 2184508964113282202784763)
                      ·
                        rfl

theorem cell23_4254316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_4254316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254316 prefixEnd_4254316 := by exact prefixLift 4254316
  have htrace : WordTrace (prefixWord ++ tailWord_4254316) baseStart_4254316 baseEnd_4254316 := by
    simpa [prefixWord, tailWord_4254316, baseEnd_4254316] using wordTrace_append hprefix tailTrace_4254316
  have hstable : (prefixWord ++ tailWord_4254316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254316).length < 2 ^ (prefixWord ++ tailWord_4254316).sum := by decide
  have hdescent : baseEnd_4254316 < baseStart_4254316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254340 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_4254340 : Nat := 118140960795 + 4254340 * 2 ^ 59
def prefixEnd_4254340 : Nat := 4983230072969 + 3 ^ 40 * 4254340 * 2
def baseEnd_4254340 : Nat := 2184521287648990108884653

theorem tailTrace_4254340 : CollatzResearch.WordTrace tailWord_4254340 prefixEnd_4254340 2184521287648990108884653 := by
  unfold tailWord_4254340
  simp only [CollatzResearch.WordTrace]
  refine ⟨77584263703630119135424237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103445684938173492180565649 77584263703630119135424237)
  ·
    refine ⟨29094098888861294675784089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77584263703630119135424237 29094098888861294675784089)
    ·
      refine ⟨21820574166645971006838067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29094098888861294675784089 21820574166645971006838067)
      ·
        refine ⟨32730861249968956510257101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21820574166645971006838067 32730861249968956510257101)
        ·
          refine ⟨12274072968738358691346413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32730861249968956510257101 12274072968738358691346413)
          ·
            refine ⟨4602777363276884509254905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12274072968738358691346413 4602777363276884509254905)
            ·
              refine ⟨3452083022457663381941179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602777363276884509254905 3452083022457663381941179)
              ·
                refine ⟨5178124533686495072911769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452083022457663381941179 5178124533686495072911769)
                ·
                  refine ⟨3883593400264871304683827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178124533686495072911769 3883593400264871304683827)
                  ·
                    refine ⟨5825390100397306957025741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3883593400264871304683827 5825390100397306957025741)
                    ·
                      refine ⟨2184521287648990108884653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825390100397306957025741 2184521287648990108884653)
                      ·
                        rfl

theorem cell23_4254340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_4254340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254340 prefixEnd_4254340 := by exact prefixLift 4254340
  have htrace : WordTrace (prefixWord ++ tailWord_4254340) baseStart_4254340 baseEnd_4254340 := by
    simpa [prefixWord, tailWord_4254340, baseEnd_4254340] using wordTrace_append hprefix tailTrace_4254340
  have hstable : (prefixWord ++ tailWord_4254340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254340).length < 2 ^ (prefixWord ++ tailWord_4254340).sum := by decide
  have hdescent : baseEnd_4254340 < baseStart_4254340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254436 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_4254436 : Nat := 118140960795 + 4254436 * 2 ^ 59
def prefixEnd_4254436 : Nat := 4983230072969 + 3 ^ 40 * 4254436 * 2
def baseEnd_4254436 : Nat := 2184570581791821733284211

theorem tailTrace_4254436 : CollatzResearch.WordTrace tailWord_4254436 prefixEnd_4254436 2184570581791821733284211 := by
  unfold tailWord_4254436
  simp only [CollatzResearch.WordTrace]
  refine ⟨77586014407456223333171581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103448019209941631110895441 77586014407456223333171581)
  ·
    refine ⟨29094755402796083749939343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77586014407456223333171581 29094755402796083749939343)
    ·
      refine ⟨43642133104194125624909015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29094755402796083749939343 43642133104194125624909015)
      ·
        refine ⟨65463199656291188437363523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43642133104194125624909015 65463199656291188437363523)
        ·
          refine ⟨98194799484436782656045285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65463199656291188437363523 98194799484436782656045285)
          ·
            refine ⟨18411524903331896748008491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98194799484436782656045285 18411524903331896748008491)
            ·
              refine ⟨27617287354997845122012737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18411524903331896748008491 27617287354997845122012737)
              ·
                refine ⟨20712965516248383841509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27617287354997845122012737 20712965516248383841509553)
                ·
                  refine ⟨15534724137186287881132165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20712965516248383841509553 15534724137186287881132165)
                  ·
                    refine ⟨2912760775722428977712281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15534724137186287881132165 2912760775722428977712281)
                    ·
                      refine ⟨2184570581791821733284211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912760775722428977712281 2184570581791821733284211)
                      ·
                        rfl

theorem cell23_4254436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_4254436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254436 prefixEnd_4254436 := by exact prefixLift 4254436
  have htrace : WordTrace (prefixWord ++ tailWord_4254436) baseStart_4254436 baseEnd_4254436 := by
    simpa [prefixWord, tailWord_4254436, baseEnd_4254436] using wordTrace_append hprefix tailTrace_4254436
  have hstable : (prefixWord ++ tailWord_4254436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254436).length < 2 ^ (prefixWord ++ tailWord_4254436).sum := by decide
  have hdescent : baseEnd_4254436 < baseStart_4254436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254446 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4254446 : Nat := 118140960795 + 4254446 * 2 ^ 59
def prefixEnd_4254446 : Nat := 4983230072969 + 3 ^ 40 * 4254446 * 2
def baseEnd_4254446 : Nat := 728191905532788898053055

theorem tailTrace_4254446 : CollatzResearch.WordTrace tailWord_4254446 prefixEnd_4254446 728191905532788898053055 := by
  unfold tailWord_4254446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396549193109527296775899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103448262363250812249471461 19396549193109527296775899)
  ·
    refine ⟨29094823789664290945163849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19396549193109527296775899 29094823789664290945163849)
    ·
      refine ⟨21821117842248218208872887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29094823789664290945163849 21821117842248218208872887)
      ·
        refine ⟨32731676763372327313309331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21821117842248218208872887 32731676763372327313309331)
        ·
          refine ⟨49097515145058490969963997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32731676763372327313309331 49097515145058490969963997)
          ·
            refine ⟨18411568179396934113736499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49097515145058490969963997 18411568179396934113736499)
            ·
              refine ⟨27617352269095401170604749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18411568179396934113736499 27617352269095401170604749)
              ·
                refine ⟨10356507100910775438976781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27617352269095401170604749 10356507100910775438976781)
                ·
                  refine ⟨3883690162841540789616293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10356507100910775438976781 3883690162841540789616293)
                  ·
                    refine ⟨728191905532788898053055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883690162841540789616293 728191905532788898053055)
                    ·
                      rfl

theorem cell23_4254446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4254446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254446 prefixEnd_4254446 := by exact prefixLift 4254446
  have htrace : WordTrace (prefixWord ++ tailWord_4254446) baseStart_4254446 baseEnd_4254446 := by
    simpa [prefixWord, tailWord_4254446, baseEnd_4254446] using wordTrace_append hprefix tailTrace_4254446
  have hstable : (prefixWord ++ tailWord_4254446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254446).length < 2 ^ (prefixWord ++ tailWord_4254446).sum := by decide
  have hdescent : baseEnd_4254446 < baseStart_4254446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254510 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_4254510 : Nat := 118140960795 + 4254510 * 2 ^ 59
def prefixEnd_4254510 : Nat := 4983230072969 + 3 ^ 40 * 4254510 * 2
def baseEnd_4254510 : Nat := 242734286595583827084319

theorem tailTrace_4254510 : CollatzResearch.WordTrace tailWord_4254510 prefixEnd_4254510 242734286595583827084319 := by
  unfold tailWord_4254510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396840977080544663067123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103449818544429571536357989 19396840977080544663067123)
  ·
    refine ⟨29095261465620816994600685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19396840977080544663067123 29095261465620816994600685)
    ·
      refine ⟨10910723049607806372975257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29095261465620816994600685 10910723049607806372975257)
      ·
        refine ⟨8183042287205854779731443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10910723049607806372975257 8183042287205854779731443)
        ·
          refine ⟨12274563430808782169597165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183042287205854779731443 12274563430808782169597165)
          ·
            refine ⟨4602961286553293313598937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12274563430808782169597165 4602961286553293313598937)
            ·
              refine ⟨3452220964914969985199203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602961286553293313598937 3452220964914969985199203)
              ·
                refine ⟨5178331447372454977798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452220964914969985199203 5178331447372454977798805)
                ·
                  refine ⟨242734286595583827084319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5178331447372454977798805 242734286595583827084319)
                  ·
                    rfl

theorem cell23_4254510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_4254510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254510 prefixEnd_4254510 := by exact prefixLift 4254510
  have htrace : WordTrace (prefixWord ++ tailWord_4254510) baseStart_4254510 baseEnd_4254510 := by
    simpa [prefixWord, tailWord_4254510, baseEnd_4254510] using wordTrace_append hprefix tailTrace_4254510
  have hstable : (prefixWord ++ tailWord_4254510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254510).length < 2 ^ (prefixWord ++ tailWord_4254510).sum := by decide
  have hdescent : baseEnd_4254510 < baseStart_4254510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254519 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 6]
def baseStart_4254519 : Nat := 118140960795 + 4254519 * 2 ^ 59
def prefixEnd_4254519 : Nat := 4983230072969 + 3 ^ 40 * 4254519 * 2
def baseEnd_4254519 : Nat := 728204400228714969515443

theorem tailTrace_4254519 : CollatzResearch.WordTrace tailWord_4254519 prefixEnd_4254519 728204400228714969515443 := by
  unfold tailWord_4254519
  simp only [CollatzResearch.WordTrace]
  refine ⟨155175056073611751841614611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103450037382407834561076407 155175056073611751841614611)
  ·
    refine ⟨232762584110417627762421917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155175056073611751841614611 232762584110417627762421917)
    ·
      refine ⟨87285969041406610410908219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232762584110417627762421917 87285969041406610410908219)
      ·
        refine ⟨130928953562109915616362329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87285969041406610410908219 130928953562109915616362329)
        ·
          refine ⟨98196715171582436712271747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130928953562109915616362329 98196715171582436712271747)
          ·
            refine ⟨147295072757373655068407621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98196715171582436712271747 147295072757373655068407621)
            ·
              refine ⟨27617826142007560325326429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147295072757373655068407621 27617826142007560325326429)
              ·
                refine ⟨10356684803252835121997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27617826142007560325326429 10356684803252835121997411)
                ·
                  refine ⟨15535027204879252682996117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10356684803252835121997411 15535027204879252682996117)
                  ·
                    refine ⟨728204400228714969515443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15535027204879252682996117 728204400228714969515443)
                    ·
                      rfl

theorem cell23_4254519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_4254519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254519 prefixEnd_4254519 := by exact prefixLift 4254519
  have htrace : WordTrace (prefixWord ++ tailWord_4254519) baseStart_4254519 baseEnd_4254519 := by
    simpa [prefixWord, tailWord_4254519, baseEnd_4254519] using wordTrace_append hprefix tailTrace_4254519
  have hstable : (prefixWord ++ tailWord_4254519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254519).length < 2 ^ (prefixWord ++ tailWord_4254519).sum := by decide
  have hdescent : baseEnd_4254519 < baseStart_4254519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254553 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_4254553 : Nat := 118140960795 + 4254553 * 2 ^ 59
def prefixEnd_4254553 : Nat := 4983230072969 + 3 ^ 40 * 4254553 * 2
def baseEnd_4254553 : Nat := 728210219676132591840391

theorem tailTrace_4254553 : CollatzResearch.WordTrace tailWord_4254553 prefixEnd_4254553 728210219676132591840391 := by
  unfold tailWord_4254553
  simp only [CollatzResearch.WordTrace]
  refine ⟨155176296155488575648352313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103450864103659050432234875 155176296155488575648352313)
  ·
    refine ⟨116382222116616431736264235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155176296155488575648352313 116382222116616431736264235)
    ·
      refine ⟨174573333174924647604396353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116382222116616431736264235 174573333174924647604396353)
      ·
        refine ⟨130929999881193485703297265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174573333174924647604396353 130929999881193485703297265)
        ·
          refine ⟨98197499910895114277472949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130929999881193485703297265 98197499910895114277472949)
          ·
            refine ⟨9206015616646416963513089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98197499910895114277472949 9206015616646416963513089)
            ·
              refine ⟨6904511712484812722634817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9206015616646416963513089 6904511712484812722634817)
              ·
                refine ⟨5178383784363609541976113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904511712484812722634817 5178383784363609541976113)
                ·
                  refine ⟨3883787838272707156482085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178383784363609541976113 3883787838272707156482085)
                  ·
                    refine ⟨728210219676132591840391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883787838272707156482085 728210219676132591840391)
                    ·
                      rfl

theorem cell23_4254553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_4254553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254553 prefixEnd_4254553 := by exact prefixLift 4254553
  have htrace : WordTrace (prefixWord ++ tailWord_4254553) baseStart_4254553 baseEnd_4254553 := by
    simpa [prefixWord, tailWord_4254553, baseEnd_4254553] using wordTrace_append hprefix tailTrace_4254553
  have hstable : (prefixWord ++ tailWord_4254553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254553).length < 2 ^ (prefixWord ++ tailWord_4254553).sum := by decide
  have hdescent : baseEnd_4254553 < baseStart_4254553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254576 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_4254576 : Nat := 118140960795 + 4254576 * 2 ^ 59
def prefixEnd_4254576 : Nat := 4983230072969 + 3 ^ 40 * 4254576 * 2
def baseEnd_4254576 : Nat := 2184642469083451185533567

theorem tailTrace_4254576 : CollatzResearch.WordTrace tailWord_4254576 prefixEnd_4254576 2184642469083451185533567 := by
  unfold tailWord_4254576
  simp only [CollatzResearch.WordTrace]
  refine ⟨77588567517202625288219791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103451423356270167050959721 77588567517202625288219791)
  ·
    refine ⟨116382851275803937932329687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77588567517202625288219791 116382851275803937932329687)
    ·
      refine ⟨174574276913705906898494531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116382851275803937932329687 174574276913705906898494531)
      ·
        refine ⟨261861415370558860347741797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174574276913705906898494531 261861415370558860347741797)
        ·
          refine ⟨49099015381979786315201587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261861415370558860347741797 49099015381979786315201587)
          ·
            refine ⟨73648523072969679472802381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49099015381979786315201587 73648523072969679472802381)
            ·
              refine ⟨27618196152363629802300893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73648523072969679472802381 27618196152363629802300893)
              ·
                refine ⟨10356823557136361175862835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27618196152363629802300893 10356823557136361175862835)
                ·
                  refine ⟨15535235335704541763794253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10356823557136361175862835 15535235335704541763794253)
                  ·
                    refine ⟨5825713250889203161422845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15535235335704541763794253 5825713250889203161422845)
                    ·
                      refine ⟨2184642469083451185533567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5825713250889203161422845 2184642469083451185533567)
                      ·
                        rfl

theorem cell23_4254576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_4254576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254576 prefixEnd_4254576 := by exact prefixLift 4254576
  have htrace : WordTrace (prefixWord ++ tailWord_4254576) baseStart_4254576 baseEnd_4254576 := by
    simpa [prefixWord, tailWord_4254576, baseEnd_4254576] using wordTrace_append hprefix tailTrace_4254576
  have hstable : (prefixWord ++ tailWord_4254576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254576).length < 2 ^ (prefixWord ++ tailWord_4254576).sum := by decide
  have hdescent : baseEnd_4254576 < baseStart_4254576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254639 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 9]
def baseStart_4254639 : Nat := 118140960795 + 4254639 * 2 ^ 59
def prefixEnd_4254639 : Nat := 4983230072969 + 3 ^ 40 * 4254639 * 2
def baseEnd_4254639 : Nat := 242741646484964937671753

theorem tailTrace_4254639 : CollatzResearch.WordTrace tailWord_4254639 prefixEnd_4254639 242741646484964937671753 := by
  unfold tailWord_4254639
  simp only [CollatzResearch.WordTrace]
  refine ⟨155179432833177012335982971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103452955222118008223988647 155179432833177012335982971)
  ·
    refine ⟨232769149249765518503974457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155179432833177012335982971 232769149249765518503974457)
    ·
      refine ⟨174576861937324138877980843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232769149249765518503974457 174576861937324138877980843)
      ·
        refine ⟨261865292905986208316971265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174576861937324138877980843 261865292905986208316971265)
        ·
          refine ⟨196398969679489656237728449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261865292905986208316971265 196398969679489656237728449)
          ·
            refine ⟨147299227259617242178296337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196398969679489656237728449 147299227259617242178296337)
            ·
              refine ⟨110474420444712931633722253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147299227259617242178296337 110474420444712931633722253)
              ·
                refine ⟨41427907666767349362645845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110474420444712931633722253 41427907666767349362645845)
                ·
                  refine ⟨242741646484964937671753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41427907666767349362645845 242741646484964937671753)
                  ·
                    rfl

theorem cell23_4254639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 9].length) (baseStart_4254639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254639 prefixEnd_4254639 := by exact prefixLift 4254639
  have htrace : WordTrace (prefixWord ++ tailWord_4254639) baseStart_4254639 baseEnd_4254639 := by
    simpa [prefixWord, tailWord_4254639, baseEnd_4254639] using wordTrace_append hprefix tailTrace_4254639
  have hstable : (prefixWord ++ tailWord_4254639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254639).length < 2 ^ (prefixWord ++ tailWord_4254639).sum := by decide
  have hdescent : baseEnd_4254639 < baseStart_4254639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254653 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_4254653 : Nat := 118140960795 + 4254653 * 2 ^ 59
def prefixEnd_4254653 : Nat := 4983230072969 + 3 ^ 40 * 4254653 * 2
def baseEnd_4254653 : Nat := 2184682007093847384270713

theorem tailTrace_4254653 : CollatzResearch.WordTrace tailWord_4254653 prefixEnd_4254653 2184682007093847384270713 := by
  unfold tailWord_4254653
  simp only [CollatzResearch.WordTrace]
  refine ⟨155179943455126292726992613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103453295636750861817995075 155179943455126292726992613)
  ·
    refine ⟨29096239397836179886311115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155179943455126292726992613 29096239397836179886311115)
    ·
      refine ⟨43644359096754269829466673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29096239397836179886311115 43644359096754269829466673)
      ·
        refine ⟨32733269322565702372100005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43644359096754269829466673 32733269322565702372100005)
        ·
          refine ⟨6137487997981069194768751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32733269322565702372100005 6137487997981069194768751)
          ·
            refine ⟨9206231996971603792153127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137487997981069194768751 9206231996971603792153127)
            ·
              refine ⟨13809347995457405688229691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9206231996971603792153127 13809347995457405688229691)
              ·
                refine ⟨20714021993186108532344537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13809347995457405688229691 20714021993186108532344537)
                ·
                  refine ⟨15535516494889581399258403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20714021993186108532344537 15535516494889581399258403)
                  ·
                    refine ⟨23303274742334372098887605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15535516494889581399258403 23303274742334372098887605)
                    ·
                      refine ⟨2184682007093847384270713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23303274742334372098887605 2184682007093847384270713)
                      ·
                        rfl

theorem cell23_4254653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_4254653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254653 prefixEnd_4254653 := by exact prefixLift 4254653
  have htrace : WordTrace (prefixWord ++ tailWord_4254653) baseStart_4254653 baseEnd_4254653 := by
    simpa [prefixWord, tailWord_4254653, baseEnd_4254653] using wordTrace_append hprefix tailTrace_4254653
  have hstable : (prefixWord ++ tailWord_4254653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254653).length < 2 ^ (prefixWord ++ tailWord_4254653).sum := by decide
  have hdescent : baseEnd_4254653 < baseStart_4254653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254662 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4254662 : Nat := 118140960795 + 4254662 * 2 ^ 59
def prefixEnd_4254662 : Nat := 4983230072969 + 3 ^ 40 * 4254662 * 2
def baseEnd_4254662 : Nat := 2184686628419737849058173

theorem tailTrace_4254662 : CollatzResearch.WordTrace tailWord_4254662 prefixEnd_4254662 2184686628419737849058173 := by
  unfold tailWord_4254662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849383491002927727002195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103453514474729124842713493 4849383491002927727002195)
  ·
    refine ⟨7274075236504391590503293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849383491002927727002195 7274075236504391590503293)
    ·
      refine ⟨2727778213689146846438735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7274075236504391590503293 2727778213689146846438735)
      ·
        refine ⟨4091667320533720269658103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727778213689146846438735 4091667320533720269658103)
        ·
          refine ⟨6137500980800580404487155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091667320533720269658103 6137500980800580404487155)
          ·
            refine ⟨9206251471200870606730733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137500980800580404487155 9206251471200870606730733)
            ·
              refine ⟨3452344301700326477524025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9206251471200870606730733 3452344301700326477524025)
              ·
                refine ⟨2589258226275244858143019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452344301700326477524025 2589258226275244858143019)
                ·
                  refine ⟨3883887339412867287214529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589258226275244858143019 3883887339412867287214529)
                  ·
                    refine ⟨2912915504559650465410897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883887339412867287214529 2912915504559650465410897)
                    ·
                      refine ⟨2184686628419737849058173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2912915504559650465410897 2184686628419737849058173)
                      ·
                        rfl

theorem cell23_4254662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4254662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254662 prefixEnd_4254662 := by exact prefixLift 4254662
  have htrace : WordTrace (prefixWord ++ tailWord_4254662) baseStart_4254662 baseEnd_4254662 := by
    simpa [prefixWord, tailWord_4254662, baseEnd_4254662] using wordTrace_append hprefix tailTrace_4254662
  have hstable : (prefixWord ++ tailWord_4254662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254662).length < 2 ^ (prefixWord ++ tailWord_4254662).sum := by decide
  have hdescent : baseEnd_4254662 < baseStart_4254662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254703 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 2, 5]
def baseStart_4254703 : Nat := 118140960795 + 4254703 * 2 ^ 59
def prefixEnd_4254703 : Nat := 4983230072969 + 3 ^ 40 * 4254703 * 2
def baseEnd_4254703 : Nat := 728235893708857396215161

theorem tailTrace_4254703 : CollatzResearch.WordTrace tailWord_4254703 prefixEnd_4254703 728235893708857396215161 := by
  unfold tailWord_4254703
  simp only [CollatzResearch.WordTrace]
  refine ⟨155181767104945151266312763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103454511403296767510875175 155181767104945151266312763)
  ·
    refine ⟨232772650657417726899469145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155181767104945151266312763 232772650657417726899469145)
    ·
      refine ⟨174579487993063295174601859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232772650657417726899469145 174579487993063295174601859)
      ·
        refine ⟨261869231989594942761902789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174579487993063295174601859 261869231989594942761902789)
        ·
          refine ⟨49100480998049051767856773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261869231989594942761902789 49100480998049051767856773)
          ·
            refine ⟨9206340187134197206473145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49100480998049051767856773 9206340187134197206473145)
            ·
              refine ⟨6904755140350647904854859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9206340187134197206473145 6904755140350647904854859)
              ·
                refine ⟨10357132710525971857282289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904755140350647904854859 10357132710525971857282289)
                ·
                  refine ⟨7767849532894478892961717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10357132710525971857282289 7767849532894478892961717)
                  ·
                    refine ⟨728235893708857396215161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7767849532894478892961717 728235893708857396215161)
                    ·
                      rfl

theorem cell23_4254703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_4254703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254703 prefixEnd_4254703 := by exact prefixLift 4254703
  have htrace : WordTrace (prefixWord ++ tailWord_4254703) baseStart_4254703 baseEnd_4254703 := by
    simpa [prefixWord, tailWord_4254703, baseEnd_4254703] using wordTrace_append hprefix tailTrace_4254703
  have hstable : (prefixWord ++ tailWord_4254703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254703).length < 2 ^ (prefixWord ++ tailWord_4254703).sum := by decide
  have hdescent : baseEnd_4254703 < baseStart_4254703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254780 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 6]
def baseStart_4254780 : Nat := 118140960795 + 4254780 * 2 ^ 59
def prefixEnd_4254780 : Nat := 4983230072969 + 3 ^ 40 * 4254780 * 2
def baseEnd_4254780 : Nat := 242749691015218709709181

theorem tailTrace_4254780 : CollatzResearch.WordTrace tailWord_4254780 prefixEnd_4254780 242749691015218709709181 := by
  unfold tailWord_4254780
  simp only [CollatzResearch.WordTrace]
  refine ⟨77592287762833096708432897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103456383683777462277910529 77592287762833096708432897)
  ·
    refine ⟨58194215822124822531324673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77592287762833096708432897 58194215822124822531324673)
    ·
      refine ⟨43645661866593616898493505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58194215822124822531324673 43645661866593616898493505)
      ·
        refine ⟨32734246399945212673870129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43645661866593616898493505 32734246399945212673870129)
        ·
          refine ⟨24550684799958909505402597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32734246399945212673870129 24550684799958909505402597)
          ·
            refine ⟨4603253399992295532262987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24550684799958909505402597 4603253399992295532262987)
            ·
              refine ⟨6904880099988443298394481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603253399992295532262987 6904880099988443298394481)
              ·
                refine ⟨5178660074991332473795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904880099988443298394481 5178660074991332473795861)
                ·
                  refine ⟨242749691015218709709181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5178660074991332473795861 242749691015218709709181)
                  ·
                    rfl

theorem cell23_4254780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_4254780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254780 prefixEnd_4254780 := by exact prefixLift 4254780
  have htrace : WordTrace (prefixWord ++ tailWord_4254780) baseStart_4254780 baseEnd_4254780 := by
    simpa [prefixWord, tailWord_4254780, baseEnd_4254780] using wordTrace_append hprefix tailTrace_4254780
  have hstable : (prefixWord ++ tailWord_4254780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254780).length < 2 ^ (prefixWord ++ tailWord_4254780).sum := by decide
  have hdescent : baseEnd_4254780 < baseStart_4254780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254797 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4254797 : Nat := 118140960795 + 4254797 * 2 ^ 59
def prefixEnd_4254797 : Nat := 4983230072969 + 3 ^ 40 * 4254797 * 2
def baseEnd_4254797 : Nat := 242750660923121646763339

theorem tailTrace_4254797 : CollatzResearch.WordTrace tailWord_4254797 prefixEnd_4254797 242750660923121646763339 := by
  unfold tailWord_4254797
  simp only [CollatzResearch.WordTrace]
  refine ⟨155185195566604605320234645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103456797044403070213489763 155185195566604605320234645)
  ·
    refine ⟨7274306042184590874385999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155185195566604605320234645 7274306042184590874385999)
    ·
      refine ⟨10911459063276886311578999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7274306042184590874385999 10911459063276886311578999)
      ·
        refine ⟨16367188594915329467368499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10911459063276886311578999 16367188594915329467368499)
        ·
          refine ⟨24550782892372994201052749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16367188594915329467368499 24550782892372994201052749)
          ·
            refine ⟨9206543584639872825394781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24550782892372994201052749 9206543584639872825394781)
            ·
              refine ⟨3452453844239952309523043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9206543584639872825394781 3452453844239952309523043)
              ·
                refine ⟨5178680766359928464284565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452453844239952309523043 5178680766359928464284565)
                ·
                  refine ⟨242750660923121646763339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5178680766359928464284565 242750660923121646763339)
                  ·
                    rfl

theorem cell23_4254797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4254797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254797 prefixEnd_4254797 := by exact prefixLift 4254797
  have htrace : WordTrace (prefixWord ++ tailWord_4254797) baseStart_4254797 baseEnd_4254797 := by
    simpa [prefixWord, tailWord_4254797, baseEnd_4254797] using wordTrace_append hprefix tailTrace_4254797
  have hstable : (prefixWord ++ tailWord_4254797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254797).length < 2 ^ (prefixWord ++ tailWord_4254797).sum := by decide
  have hdescent : baseEnd_4254797 < baseStart_4254797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254841 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 1, 1, 3]
def baseStart_4254841 : Nat := 118140960795 + 4254841 * 2 ^ 59
def prefixEnd_4254841 : Nat := 4983230072969 + 3 ^ 40 * 4254841 * 2
def baseEnd_4254841 : Nat := 2184778541456892648719849

theorem tailTrace_4254841 : CollatzResearch.WordTrace tailWord_4254841 prefixEnd_4254841 2184778541456892648719849 := by
  unfold tailWord_4254841
  simp only [CollatzResearch.WordTrace]
  refine ⟨155186800378445200834836377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103457866918963467223224251 155186800378445200834836377)
  ·
    refine ⟨116390100283833900626127283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155186800378445200834836377 116390100283833900626127283)
    ·
      refine ⟨174585150425750850939190925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116390100283833900626127283 174585150425750850939190925)
      ·
        refine ⟨65469431409656569102196597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174585150425750850939190925 65469431409656569102196597)
        ·
          refine ⟨6137759194655303353330931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65469431409656569102196597 6137759194655303353330931)
          ·
            refine ⟨9206638791982955029996397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137759194655303353330931 9206638791982955029996397)
            ·
              refine ⟨3452489546993608136248649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9206638791982955029996397 3452489546993608136248649)
              ·
                refine ⟨2589367160245206102186487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452489546993608136248649 2589367160245206102186487)
                ·
                  refine ⟨3884050740367809153279731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589367160245206102186487 3884050740367809153279731)
                  ·
                    refine ⟨5826076110551713729919597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884050740367809153279731 5826076110551713729919597)
                    ·
                      refine ⟨2184778541456892648719849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826076110551713729919597 2184778541456892648719849)
                      ·
                        rfl

theorem cell23_4254841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_4254841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254841 prefixEnd_4254841 := by exact prefixLift 4254841
  have htrace : WordTrace (prefixWord ++ tailWord_4254841) baseStart_4254841 baseEnd_4254841 := by
    simpa [prefixWord, tailWord_4254841, baseEnd_4254841] using wordTrace_append hprefix tailTrace_4254841
  have hstable : (prefixWord ++ tailWord_4254841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254841).length < 2 ^ (prefixWord ++ tailWord_4254841).sum := by decide
  have hdescent : baseEnd_4254841 < baseStart_4254841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254857 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_4254857 : Nat := 118140960795 + 4254857 * 2 ^ 59
def prefixEnd_4254857 : Nat := 4983230072969 + 3 ^ 40 * 4254857 * 2
def baseEnd_4254857 : Nat := 728262252382454862039925

theorem tailTrace_4254857 : CollatzResearch.WordTrace tailWord_4254857 prefixEnd_4254857 728262252382454862039925 := by
  unfold tailWord_4254857
  simp only [CollatzResearch.WordTrace]
  refine ⟨155187383946387235567418825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103458255964258157044945883 155187383946387235567418825)
  ·
    refine ⟨116390537959790426675564119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155187383946387235567418825 116390537959790426675564119)
    ·
      refine ⟨174585806939685640013346179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116390537959790426675564119 174585806939685640013346179)
      ·
        refine ⟨261878710409528460020019269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174585806939685640013346179 261878710409528460020019269)
        ·
          refine ⟨49102258201786586253753613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261878710409528460020019269 49102258201786586253753613)
          ·
            refine ⟨18413346825669969845157605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49102258201786586253753613 18413346825669969845157605)
            ·
              refine ⟨3452502529813119345967051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18413346825669969845157605 3452502529813119345967051)
              ·
                refine ⟨5178753794719679018950577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452502529813119345967051 5178753794719679018950577)
                ·
                  refine ⟨3884065346039759264212933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178753794719679018950577 3884065346039759264212933)
                  ·
                    refine ⟨728262252382454862039925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3884065346039759264212933 728262252382454862039925)
                    ·
                      rfl

theorem cell23_4254857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_4254857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254857 prefixEnd_4254857 := by exact prefixLift 4254857
  have htrace : WordTrace (prefixWord ++ tailWord_4254857) baseStart_4254857 baseEnd_4254857 := by
    simpa [prefixWord, tailWord_4254857, baseEnd_4254857] using wordTrace_append hprefix tailTrace_4254857
  have hstable : (prefixWord ++ tailWord_4254857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254857).length < 2 ^ (prefixWord ++ tailWord_4254857).sum := by decide
  have hdescent : baseEnd_4254857 < baseStart_4254857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254880 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_4254880 : Nat := 118140960795 + 4254880 * 2 ^ 59
def prefixEnd_4254880 : Nat := 4983230072969 + 3 ^ 40 * 4254880 * 2
def baseEnd_4254880 : Nat := 2184798567202417996132169

theorem tailTrace_4254880 : CollatzResearch.WordTrace tailWord_4254880 prefixEnd_4254880 2184798567202417996132169 := by
  unfold tailWord_4254880
  simp only [CollatzResearch.WordTrace]
  refine ⟨77594111412651955247753047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103458815216869273663670729 77594111412651955247753047)
  ·
    refine ⟨116391167118977932871629571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77594111412651955247753047 116391167118977932871629571)
    ·
      refine ⟨174586750678466899307444357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116391167118977932871629571 174586750678466899307444357)
      ·
        refine ⟨32735015752212543620145817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174586750678466899307444357 32735015752212543620145817)
        ·
          refine ⟨24551261814159407715109363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32735015752212543620145817 24551261814159407715109363)
          ·
            refine ⟨36826892721239111572664045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24551261814159407715109363 36826892721239111572664045)
            ·
              refine ⟨13810084770464666839749017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36826892721239111572664045 13810084770464666839749017)
              ·
                refine ⟨10357563577848500129811763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13810084770464666839749017 10357563577848500129811763)
                ·
                  refine ⟨15536345366772750194717645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10357563577848500129811763 15536345366772750194717645)
                  ·
                    refine ⟨5826129512539781323019117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15536345366772750194717645 5826129512539781323019117)
                    ·
                      refine ⟨2184798567202417996132169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826129512539781323019117 2184798567202417996132169)
                      ·
                        rfl

theorem cell23_4254880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_4254880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254880 prefixEnd_4254880 := by exact prefixLift 4254880
  have htrace : WordTrace (prefixWord ++ tailWord_4254880) baseStart_4254880 baseEnd_4254880 := by
    simpa [prefixWord, tailWord_4254880, baseEnd_4254880] using wordTrace_append hprefix tailTrace_4254880
  have hstable : (prefixWord ++ tailWord_4254880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254880).length < 2 ^ (prefixWord ++ tailWord_4254880).sum := by decide
  have hdescent : baseEnd_4254880 < baseStart_4254880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254884 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_4254884 : Nat := 118140960795 + 4254884 * 2 ^ 59
def prefixEnd_4254884 : Nat := 4983230072969 + 3 ^ 40 * 4254884 * 2
def baseEnd_4254884 : Nat := 2184800621125035980482151

theorem tailTrace_4254884 : CollatzResearch.WordTrace tailWord_4254884 prefixEnd_4254884 2184800621125035980482151 := by
  unfold tailWord_4254884
  simp only [CollatzResearch.WordTrace]
  refine ⟨77594184358644709589325853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103458912478192946119101137 77594184358644709589325853)
  ·
    refine ⟨29097819134491766095997195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77594184358644709589325853 29097819134491766095997195)
    ·
      refine ⟨43646728701737649143995793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29097819134491766095997195 43646728701737649143995793)
      ·
        refine ⟨32735046526303236857996845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43646728701737649143995793 32735046526303236857996845)
        ·
          refine ⟨12275642447363713821748817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32735046526303236857996845 12275642447363713821748817)
          ·
            refine ⟨9206731835522785366311613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12275642447363713821748817 9206731835522785366311613)
            ·
              refine ⟨3452524438321044512366855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9206731835522785366311613 3452524438321044512366855)
              ·
                refine ⟨5178786657481566768550283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452524438321044512366855 5178786657481566768550283)
                ·
                  refine ⟨7768179986222350152825425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178786657481566768550283 7768179986222350152825425)
                  ·
                    refine ⟨5826134989666762614619069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7768179986222350152825425 5826134989666762614619069)
                    ·
                      refine ⟨2184800621125035980482151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826134989666762614619069 2184800621125035980482151)
                      ·
                        rfl

theorem cell23_4254884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_4254884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254884 prefixEnd_4254884 := by exact prefixLift 4254884
  have htrace : WordTrace (prefixWord ++ tailWord_4254884) baseStart_4254884 baseEnd_4254884 := by
    simpa [prefixWord, tailWord_4254884, baseEnd_4254884] using wordTrace_append hprefix tailTrace_4254884
  have hstable : (prefixWord ++ tailWord_4254884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254884).length < 2 ^ (prefixWord ++ tailWord_4254884).sum := by decide
  have hdescent : baseEnd_4254884 < baseStart_4254884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254898 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_4254898 : Nat := 118140960795 + 4254898 * 2 ^ 59
def prefixEnd_4254898 : Nat := 4983230072969 + 3 ^ 40 * 4254898 * 2
def baseEnd_4254898 : Nat := 2184807809854198925707087

theorem tailTrace_4254898 : CollatzResearch.WordTrace tailWord_4254898 prefixEnd_4254898 2184807809854198925707087 := by
  unfold tailWord_4254898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38797219834809674892415337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103459252892825799713107565 38797219834809674892415337)
  ·
    refine ⟨29097914876107256169311503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38797219834809674892415337 29097914876107256169311503)
    ·
      refine ⟨43646872314160884253967255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29097914876107256169311503 43646872314160884253967255)
      ·
        refine ⟨65470308471241326380950883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43646872314160884253967255 65470308471241326380950883)
        ·
          refine ⟨98205462706861989571426325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65470308471241326380950883 98205462706861989571426325)
          ·
            refine ⟨4603381064384155761160609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98205462706861989571426325 4603381064384155761160609)
            ·
              refine ⟨3452535798288116820870457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603381064384155761160609 3452535798288116820870457)
              ·
                refine ⟨2589401848716087615652843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452535798288116820870457 2589401848716087615652843)
                ·
                  refine ⟨3884102773074131423479265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589401848716087615652843 3884102773074131423479265)
                  ·
                    refine ⟨2913077079805598567609449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884102773074131423479265 2913077079805598567609449)
                    ·
                      refine ⟨2184807809854198925707087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913077079805598567609449 2184807809854198925707087)
                      ·
                        rfl

theorem cell23_4254898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_4254898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254898 prefixEnd_4254898 := by exact prefixLift 4254898
  have htrace : WordTrace (prefixWord ++ tailWord_4254898) baseStart_4254898 baseEnd_4254898 := by
    simpa [prefixWord, tailWord_4254898, baseEnd_4254898] using wordTrace_append hprefix tailTrace_4254898
  have hstable : (prefixWord ++ tailWord_4254898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254898).length < 2 ^ (prefixWord ++ tailWord_4254898).sum := by decide
  have hdescent : baseEnd_4254898 < baseStart_4254898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254903 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_4254903 : Nat := 118140960795 + 4254903 * 2 ^ 59
def prefixEnd_4254903 : Nat := 4983230072969 + 3 ^ 40 * 4254903 * 2
def baseEnd_4254903 : Nat := 2184810377257471406144563

theorem tailTrace_4254903 : CollatzResearch.WordTrace tailWord_4254903 prefixEnd_4254903 2184810377257471406144563 := by
  unfold tailWord_4254903
  simp only [CollatzResearch.WordTrace]
  refine ⟨155189061704220585423593363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103459374469480390282395575 155189061704220585423593363)
  ·
    refine ⟨232783592556330878135390045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155189061704220585423593363 232783592556330878135390045)
    ·
      refine ⟨87293847208624079300771267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232783592556330878135390045 87293847208624079300771267)
      ·
        refine ⟨130940770812936118951156901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87293847208624079300771267 130940770812936118951156901)
        ·
          refine ⟨24551394527425522303341919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130940770812936118951156901 24551394527425522303341919)
          ·
            refine ⟨36827091791138283455012879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24551394527425522303341919 36827091791138283455012879)
            ·
              refine ⟨55240637686707425182519319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36827091791138283455012879 55240637686707425182519319)
              ·
                refine ⟨82860956530061137773778979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55240637686707425182519319 82860956530061137773778979)
                ·
                  refine ⟨124291434795091706660668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82860956530061137773778979 124291434795091706660668469)
                  ·
                    refine ⟨11652322012039847499437669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124291434795091706660668469 11652322012039847499437669)
                    ·
                      refine ⟨2184810377257471406144563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11652322012039847499437669 2184810377257471406144563)
                      ·
                        rfl

theorem cell23_4254903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_4254903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254903 prefixEnd_4254903 := by exact prefixLift 4254903
  have htrace : WordTrace (prefixWord ++ tailWord_4254903) baseStart_4254903 baseEnd_4254903 := by
    simpa [prefixWord, tailWord_4254903, baseEnd_4254903] using wordTrace_append hprefix tailTrace_4254903
  have hstable : (prefixWord ++ tailWord_4254903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254903).length < 2 ^ (prefixWord ++ tailWord_4254903).sum := by decide
  have hdescent : baseEnd_4254903 < baseStart_4254903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254923 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_4254923 : Nat := 118140960795 + 4254923 * 2 ^ 59
def prefixEnd_4254923 : Nat := 4983230072969 + 3 ^ 40 * 4254923 * 2
def baseEnd_4254923 : Nat := 2184820646870561327894471

theorem tailTrace_4254923 : CollatzResearch.WordTrace tailWord_4254923 prefixEnd_4254923 2184820646870561327894471 := by
  unfold tailWord_4254923
  simp only [CollatzResearch.WordTrace]
  refine ⟨155189791164148128839321423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103459860776098752559547615 155189791164148128839321423)
  ·
    refine ⟨232784686746222193258982135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155189791164148128839321423 232784686746222193258982135)
    ·
      refine ⟨349177030119333289888473203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232784686746222193258982135 349177030119333289888473203)
      ·
        refine ⟨523765545178999934832709805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349177030119333289888473203 523765545178999934832709805)
        ·
          refine ⟨196412079442124975562266177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523765545178999934832709805 196412079442124975562266177)
          ·
            refine ⟨147309059581593731671699633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196412079442124975562266177 147309059581593731671699633)
            ·
              refine ⟨110481794686195298753774725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147309059581593731671699633 110481794686195298753774725)
              ·
                refine ⟨20715336503661618516332761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110481794686195298753774725 20715336503661618516332761)
                ·
                  refine ⟨15536502377746213887249571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20715336503661618516332761 15536502377746213887249571)
                  ·
                    refine ⟨23304753566619320830874357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15536502377746213887249571 23304753566619320830874357)
                    ·
                      refine ⟨2184820646870561327894471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23304753566619320830874357 2184820646870561327894471)
                      ·
                        rfl

theorem cell23_4254923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_4254923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254923 prefixEnd_4254923 := by exact prefixLift 4254923
  have htrace : WordTrace (prefixWord ++ tailWord_4254923) baseStart_4254923 baseEnd_4254923 := by
    simpa [prefixWord, tailWord_4254923, baseEnd_4254923] using wordTrace_append hprefix tailTrace_4254923
  have hstable : (prefixWord ++ tailWord_4254923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254923).length < 2 ^ (prefixWord ++ tailWord_4254923).sum := by decide
  have hdescent : baseEnd_4254923 < baseStart_4254923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254937 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 4, 2, 2]
def baseStart_4254937 : Nat := 118140960795 + 4254937 * 2 ^ 59
def prefixEnd_4254937 : Nat := 4983230072969 + 3 ^ 40 * 4254937 * 2
def baseEnd_4254937 : Nat := 2184827835599724273119407

theorem tailTrace_4254937 : CollatzResearch.WordTrace tailWord_4254937 prefixEnd_4254937 2184827835599724273119407 := by
  unfold tailWord_4254937
  simp only [CollatzResearch.WordTrace]
  refine ⟨155190301786097409230331065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103460201190731606153554043 155190301786097409230331065)
  ·
    refine ⟨116392726339573056922748299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155190301786097409230331065 116392726339573056922748299)
    ·
      refine ⟨174589089509359585384122449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116392726339573056922748299 174589089509359585384122449)
      ·
        refine ⟨130941817132019689038091837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174589089509359585384122449 130941817132019689038091837)
        ·
          refine ⟨49103181424507383389284439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130941817132019689038091837 49103181424507383389284439)
          ·
            refine ⟨73654772136761075083926659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49103181424507383389284439 73654772136761075083926659)
            ·
              refine ⟨110482158205141612625889989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73654772136761075083926659 110482158205141612625889989)
              ·
                refine ⟨20715404663464052367354373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110482158205141612625889989 20715404663464052367354373)
                ·
                  refine ⟨3884138374399509818878945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20715404663464052367354373 3884138374399509818878945)
                  ·
                    refine ⟨2913103780799632364159209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884138374399509818878945 2913103780799632364159209)
                    ·
                      refine ⟨2184827835599724273119407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913103780799632364159209 2184827835599724273119407)
                      ·
                        rfl

theorem cell23_4254937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_4254937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254937 prefixEnd_4254937 := by exact prefixLift 4254937
  have htrace : WordTrace (prefixWord ++ tailWord_4254937) baseStart_4254937 baseEnd_4254937 := by
    simpa [prefixWord, tailWord_4254937, baseEnd_4254937] using wordTrace_append hprefix tailTrace_4254937
  have hstable : (prefixWord ++ tailWord_4254937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254937).length < 2 ^ (prefixWord ++ tailWord_4254937).sum := by decide
  have hdescent : baseEnd_4254937 < baseStart_4254937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254941 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4254941 : Nat := 118140960795 + 4254941 * 2 ^ 59
def prefixEnd_4254941 : Nat := 4983230072969 + 3 ^ 40 * 4254941 * 2
def baseEnd_4254941 : Nat := 2184829889522342257469389

theorem tailTrace_4254941 : CollatzResearch.WordTrace tailWord_4254941 prefixEnd_4254941 2184829889522342257469389 := by
  unfold tailWord_4254941
  simp only [CollatzResearch.WordTrace]
  refine ⟨155190447678082917913476677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103460298452055278608984451 155190447678082917913476677)
  ·
    refine ⟨29098208939640547108776877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155190447678082917913476677 29098208939640547108776877)
    ·
      refine ⟨10911828352365205165791329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29098208939640547108776877 10911828352365205165791329)
      ·
        refine ⟨8183871264273903874343497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10911828352365205165791329 8183871264273903874343497)
        ·
          refine ⟨6137903448205427905757623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8183871264273903874343497 6137903448205427905757623)
          ·
            refine ⟨9206855172308141858636435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137903448205427905757623 9206855172308141858636435)
            ·
              refine ⟨13810282758462212787954653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9206855172308141858636435 13810282758462212787954653)
              ·
                refine ⟨5178856034423329795482995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13810282758462212787954653 5178856034423329795482995)
                ·
                  refine ⟨7768284051634994693224493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178856034423329795482995 7768284051634994693224493)
                  ·
                    refine ⟨2913106519363123009959185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7768284051634994693224493 2913106519363123009959185)
                    ·
                      refine ⟨2184829889522342257469389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913106519363123009959185 2184829889522342257469389)
                      ·
                        rfl

theorem cell23_4254941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4254941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254941 prefixEnd_4254941 := by exact prefixLift 4254941
  have htrace : WordTrace (prefixWord ++ tailWord_4254941) baseStart_4254941 baseEnd_4254941 := by
    simpa [prefixWord, tailWord_4254941, baseEnd_4254941] using wordTrace_append hprefix tailTrace_4254941
  have hstable : (prefixWord ++ tailWord_4254941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254941).length < 2 ^ (prefixWord ++ tailWord_4254941).sum := by decide
  have hdescent : baseEnd_4254941 < baseStart_4254941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254954 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_4254954 : Nat := 118140960795 + 4254954 * 2 ^ 59
def prefixEnd_4254954 : Nat := 4983230072969 + 3 ^ 40 * 4254954 * 2
def baseEnd_4254954 : Nat := 2184836564770850706606829

theorem tailTrace_4254954 : CollatzResearch.WordTrace tailWord_4254954 prefixEnd_4254954 2184836564770850706606829 := by
  unfold tailWord_4254954
  simp only [CollatzResearch.WordTrace]
  refine ⟨38797730456758955283424979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103460614551357214089133277 38797730456758955283424979)
  ·
    refine ⟨58196595685138432925137469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38797730456758955283424979 58196595685138432925137469)
    ·
      refine ⟨21823723381926912346926551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58196595685138432925137469 21823723381926912346926551)
      ·
        refine ⟨32735585072890368520389827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21823723381926912346926551 32735585072890368520389827)
        ·
          refine ⟨49103377609335552780584741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32735585072890368520389827 49103377609335552780584741)
          ·
            refine ⟨9206883301750416146359639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49103377609335552780584741 9206883301750416146359639)
            ·
              refine ⟨13810324952625624219539459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9206883301750416146359639 13810324952625624219539459)
              ·
                refine ⟨20715487428938436329309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13810324952625624219539459 20715487428938436329309189)
                ·
                  refine ⟨3884153892925956811745473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20715487428938436329309189 3884153892925956811745473)
                  ·
                    refine ⟨2913115419694467608809105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884153892925956811745473 2913115419694467608809105)
                    ·
                      refine ⟨2184836564770850706606829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913115419694467608809105 2184836564770850706606829)
                      ·
                        rfl

theorem cell23_4254954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_4254954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254954 prefixEnd_4254954 := by exact prefixLift 4254954
  have htrace : WordTrace (prefixWord ++ tailWord_4254954) baseStart_4254954 baseEnd_4254954 := by
    simpa [prefixWord, tailWord_4254954, baseEnd_4254954] using wordTrace_append hprefix tailTrace_4254954
  have hstable : (prefixWord ++ tailWord_4254954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254954).length < 2 ^ (prefixWord ++ tailWord_4254954).sum := by decide
  have hdescent : baseEnd_4254954 < baseStart_4254954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254970 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_4254970 : Nat := 118140960795 + 4254970 * 2 ^ 59
def prefixEnd_4254970 : Nat := 4983230072969 + 3 ^ 40 * 4254970 * 2
def baseEnd_4254970 : Nat := 2184844780461322644006755

theorem tailTrace_4254970 : CollatzResearch.WordTrace tailWord_4254970 prefixEnd_4254970 2184844780461322644006755 := by
  unfold tailWord_4254970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38797876348744463966570591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103461003596651903910854909 38797876348744463966570591)
  ·
    refine ⟨58196814523116695949855887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38797876348744463966570591 58196814523116695949855887)
    ·
      refine ⟨87295221784675043924783831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58196814523116695949855887 87295221784675043924783831)
      ·
        refine ⟨130942832677012565887175747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87295221784675043924783831 130942832677012565887175747)
        ·
          refine ⟨196414249015518848830763621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130942832677012565887175747 196414249015518848830763621)
          ·
            refine ⟨36827671690409784155768179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196414249015518848830763621 36827671690409784155768179)
            ·
              refine ⟨55241507535614676233652269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36827671690409784155768179 55241507535614676233652269)
              ·
                refine ⟨20715565325855503587619601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55241507535614676233652269 20715565325855503587619601)
                ·
                  refine ⟨15536673994391627690714701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20715565325855503587619601 15536673994391627690714701)
                  ·
                    refine ⟨5826252747896860384018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15536673994391627690714701 5826252747896860384018013)
                    ·
                      refine ⟨2184844780461322644006755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826252747896860384018013 2184844780461322644006755)
                      ·
                        rfl

theorem cell23_4254970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_4254970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254970 prefixEnd_4254970 := by exact prefixLift 4254970
  have htrace : WordTrace (prefixWord ++ tailWord_4254970) baseStart_4254970 baseEnd_4254970 := by
    simpa [prefixWord, tailWord_4254970, baseEnd_4254970] using wordTrace_append hprefix tailTrace_4254970
  have hstable : (prefixWord ++ tailWord_4254970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254970).length < 2 ^ (prefixWord ++ tailWord_4254970).sum := by decide
  have hdescent : baseEnd_4254970 < baseStart_4254970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4254990 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_4254990 : Nat := 118140960795 + 4254990 * 2 ^ 59
def prefixEnd_4254990 : Nat := 4983230072969 + 3 ^ 40 * 4254990 * 2
def baseEnd_4254990 : Nat := 728285016691470855252221

theorem tailTrace_4254990 : CollatzResearch.WordTrace tailWord_4254990 prefixEnd_4254990 728285016691470855252221 := by
  unfold tailWord_4254990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399029356863174910251303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103461489903270266188006949 19399029356863174910251303)
  ·
    refine ⟨29098544035294762365376955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19399029356863174910251303 29098544035294762365376955)
    ·
      refine ⟨43647816052942143548065433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29098544035294762365376955 43647816052942143548065433)
      ·
        refine ⟨32735862039706607661049075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43647816052942143548065433 32735862039706607661049075)
        ·
          refine ⟨49103793059559911491573613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32735862039706607661049075 49103793059559911491573613)
          ·
            refine ⟨18413922397334966809340105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49103793059559911491573613 18413922397334966809340105)
            ·
              refine ⟨13810441798001225107005079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18413922397334966809340105 13810441798001225107005079)
              ·
                refine ⟨20715662697001837660507619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13810441798001225107005079 20715662697001837660507619)
                ·
                  refine ⟨31073494045502756490761429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20715662697001837660507619 31073494045502756490761429)
                  ·
                    refine ⟨728285016691470855252221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31073494045502756490761429 728285016691470855252221)
                    ·
                      rfl

theorem cell23_4254990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_4254990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4254990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4254990 prefixEnd_4254990 := by exact prefixLift 4254990
  have htrace : WordTrace (prefixWord ++ tailWord_4254990) baseStart_4254990 baseEnd_4254990 := by
    simpa [prefixWord, tailWord_4254990, baseEnd_4254990] using wordTrace_append hprefix tailTrace_4254990
  have hstable : (prefixWord ++ tailWord_4254990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4254990).length < 2 ^ (prefixWord ++ tailWord_4254990).sum := by decide
  have hdescent : baseEnd_4254990 < baseStart_4254990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4254990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255007 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 2, 5]
def baseStart_4255007 : Nat := 118140960795 + 4255007 * 2 ^ 59
def prefixEnd_4255007 : Nat := 4983230072969 + 3 ^ 40 * 4255007 * 2
def baseEnd_4255007 : Nat := 728287926415179666414695

theorem tailTrace_4255007 : CollatzResearch.WordTrace tailWord_4255007 prefixEnd_4255007 728287926415179666414695 := by
  unfold tailWord_4255007
  simp only [CollatzResearch.WordTrace]
  refine ⟨155192854895843811185379275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103461903263895874123586183 155192854895843811185379275)
  ·
    refine ⟨232789282343765716778068913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155192854895843811185379275 232789282343765716778068913)
    ·
      refine ⟨174591961757824287583551685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232789282343765716778068913 174591961757824287583551685)
      ·
        refine ⟨32735992829592053921915941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174591961757824287583551685 32735992829592053921915941)
        ·
          refine ⟨6137998655548510110359239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32735992829592053921915941 6137998655548510110359239)
          ·
            refine ⟨9206997983322765165538859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137998655548510110359239 9206997983322765165538859)
            ·
              refine ⟨13810496974984147748308289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9206997983322765165538859 13810496974984147748308289)
              ·
                refine ⟨10357872731238110811231217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13810496974984147748308289 10357872731238110811231217)
                ·
                  refine ⟨7768404548428583108423413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10357872731238110811231217 7768404548428583108423413)
                  ·
                    refine ⟨728287926415179666414695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7768404548428583108423413 728287926415179666414695)
                    ·
                      rfl

theorem cell23_4255007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_4255007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255007 prefixEnd_4255007 := by exact prefixLift 4255007
  have htrace : WordTrace (prefixWord ++ tailWord_4255007) baseStart_4255007 baseEnd_4255007 := by
    simpa [prefixWord, tailWord_4255007, baseEnd_4255007] using wordTrace_append hprefix tailTrace_4255007
  have hstable : (prefixWord ++ tailWord_4255007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255007).length < 2 ^ (prefixWord ++ tailWord_4255007).sum := by decide
  have hdescent : baseEnd_4255007 < baseStart_4255007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255044 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4255044 : Nat := 118140960795 + 4255044 * 2 ^ 59
def prefixEnd_4255044 : Nat := 4983230072969 + 3 ^ 40 * 4255044 * 2
def baseEnd_4255044 : Nat := 2184882778029755354481415

theorem tailTrace_4255044 : CollatzResearch.WordTrace tailWord_4255044 prefixEnd_4255044 2184882778029755354481415 := by
  unfold tailWord_4255044
  simp only [CollatzResearch.WordTrace]
  refine ⟨77597102198354883252238093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103462802931139844336317457 77597102198354883252238093)
  ·
    refine ⟨29098913324383081219589285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77597102198354883252238093 29098913324383081219589285)
    ·
      refine ⟨5456046248321827728672991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29098913324383081219589285 5456046248321827728672991)
      ·
        refine ⟨8184069372482741593009487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456046248321827728672991 8184069372482741593009487)
        ·
          refine ⟨12276104058724112389514231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8184069372482741593009487 12276104058724112389514231)
          ·
            refine ⟨18414156088086168584271347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12276104058724112389514231 18414156088086168584271347)
            ·
              refine ⟨27621234132129252876407021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18414156088086168584271347 27621234132129252876407021)
              ·
                refine ⟨10357962799548469828652633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27621234132129252876407021 10357962799548469828652633)
                ·
                  refine ⟨7768472099661352371489475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10357962799548469828652633 7768472099661352371489475)
                  ·
                    refine ⟨11652708149492028557234213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7768472099661352371489475 11652708149492028557234213)
                    ·
                      refine ⟨2184882778029755354481415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11652708149492028557234213 2184882778029755354481415)
                      ·
                        rfl

theorem cell23_4255044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4255044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255044 prefixEnd_4255044 := by exact prefixLift 4255044
  have htrace : WordTrace (prefixWord ++ tailWord_4255044) baseStart_4255044 baseEnd_4255044 := by
    simpa [prefixWord, tailWord_4255044, baseEnd_4255044] using wordTrace_append hprefix tailTrace_4255044
  have hstable : (prefixWord ++ tailWord_4255044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255044).length < 2 ^ (prefixWord ++ tailWord_4255044).sum := by decide
  have hdescent : baseEnd_4255044 < baseStart_4255044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255047 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_4255047 : Nat := 118140960795 + 4255047 * 2 ^ 59
def prefixEnd_4255047 : Nat := 4983230072969 + 3 ^ 40 * 4255047 * 2
def baseEnd_4255047 : Nat := 2184884318471718842743901

theorem tailTrace_4255047 : CollatzResearch.WordTrace tailWord_4255047 prefixEnd_4255047 2184884318471718842743901 := by
  unfold tailWord_4255047
  simp only [CollatzResearch.WordTrace]
  refine ⟨155194313815698898016835395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103462875877132598677890263 155194313815698898016835395)
  ·
    refine ⟨232791470723548347025253093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155194313815698898016835395 232791470723548347025253093)
    ·
      refine ⟨43648400760665315067234955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232791470723548347025253093 43648400760665315067234955)
      ·
        refine ⟨65472601140997972600852433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43648400760665315067234955 65472601140997972600852433)
        ·
          refine ⟨49104450855748479450639325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65472601140997972600852433 49104450855748479450639325)
          ·
            refine ⟨18414169070905679793989747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49104450855748479450639325 18414169070905679793989747)
            ·
              refine ⟨27621253606358519690984621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18414169070905679793989747 27621253606358519690984621)
              ·
                refine ⟨10357970102384444884119233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27621253606358519690984621 10357970102384444884119233)
                ·
                  refine ⟨7768477576788333663089425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10357970102384444884119233 7768477576788333663089425)
                  ·
                    refine ⟨5826358182591250247317069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7768477576788333663089425 5826358182591250247317069)
                    ·
                      refine ⟨2184884318471718842743901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826358182591250247317069 2184884318471718842743901)
                      ·
                        rfl

theorem cell23_4255047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_4255047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255047 prefixEnd_4255047 := by exact prefixLift 4255047
  have htrace : WordTrace (prefixWord ++ tailWord_4255047) baseStart_4255047 baseEnd_4255047 := by
    simpa [prefixWord, tailWord_4255047, baseEnd_4255047] using wordTrace_append hprefix tailTrace_4255047
  have hstable : (prefixWord ++ tailWord_4255047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255047).length < 2 ^ (prefixWord ++ tailWord_4255047).sum := by decide
  have hdescent : baseEnd_4255047 < baseStart_4255047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255054 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_4255054 : Nat := 118140960795 + 4255054 * 2 ^ 59
def prefixEnd_4255054 : Nat := 4983230072969 + 3 ^ 40 * 4255054 * 2
def baseEnd_4255054 : Nat := 728295970945433438452123

theorem tailTrace_4255054 : CollatzResearch.WordTrace tailWord_4255054 prefixEnd_4255054 728295970945433438452123 := by
  unfold tailWord_4255054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399321140834192276542527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103463046084449025474893477 19399321140834192276542527)
  ·
    refine ⟨29098981711251288414813791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19399321140834192276542527 29098981711251288414813791)
    ·
      refine ⟨43648472566876932622220687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29098981711251288414813791 43648472566876932622220687)
      ·
        refine ⟨65472708850315398933331031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43648472566876932622220687 65472708850315398933331031)
        ·
          refine ⟨98209063275473098399996547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65472708850315398933331031 98209063275473098399996547)
          ·
            refine ⟨147313594913209647599994821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98209063275473098399996547 147313594913209647599994821)
            ·
              refine ⟨27621299046226808924999029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147313594913209647599994821 27621299046226808924999029)
              ·
                refine ⟨2589496785583763336718659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27621299046226808924999029 2589496785583763336718659)
                ·
                  refine ⟨3884245178375645005077989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589496785583763336718659 3884245178375645005077989)
                  ·
                    refine ⟨728295970945433438452123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3884245178375645005077989 728295970945433438452123)
                    ·
                      rfl

theorem cell23_4255054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_4255054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255054 prefixEnd_4255054 := by exact prefixLift 4255054
  have htrace : WordTrace (prefixWord ++ tailWord_4255054) baseStart_4255054 baseEnd_4255054 := by
    simpa [prefixWord, tailWord_4255054, baseEnd_4255054] using wordTrace_append hprefix tailTrace_4255054
  have hstable : (prefixWord ++ tailWord_4255054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255054).length < 2 ^ (prefixWord ++ tailWord_4255054).sum := by decide
  have hdescent : baseEnd_4255054 < baseStart_4255054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255062 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4255062 : Nat := 118140960795 + 4255062 * 2 ^ 59
def prefixEnd_4255062 : Nat := 4983230072969 + 3 ^ 40 * 4255062 * 2
def baseEnd_4255062 : Nat := 242765780075726253784037

theorem tailTrace_4255062 : CollatzResearch.WordTrace tailWord_4255062 prefixEnd_4255062 242765780075726253784037 := by
  unfold tailWord_4255062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699678806915284723664465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103463240607096370385754293 9699678806915284723664465)
  ·
    refine ⟨7274759105186463542748349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9699678806915284723664465 7274759105186463542748349)
    ·
      refine ⟨2728034664444923828530631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7274759105186463542748349 2728034664444923828530631)
      ·
        refine ⟨4092051996667385742795947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728034664444923828530631 4092051996667385742795947)
        ·
          refine ⟨6138077995001078614193921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092051996667385742795947 6138077995001078614193921)
          ·
            refine ⟨4603558496250808960645441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6138077995001078614193921 4603558496250808960645441)
            ·
              refine ⟨3452668872188106720484081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603558496250808960645441 3452668872188106720484081)
              ·
                refine ⟨2589501654141080040363061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452668872188106720484081 2589501654141080040363061)
                ·
                  refine ⟨242765780075726253784037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2589501654141080040363061 242765780075726253784037)
                  ·
                    rfl

theorem cell23_4255062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4255062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255062 prefixEnd_4255062 := by exact prefixLift 4255062
  have htrace : WordTrace (prefixWord ++ tailWord_4255062) baseStart_4255062 baseEnd_4255062 := by
    simpa [prefixWord, tailWord_4255062, baseEnd_4255062] using wordTrace_append hprefix tailTrace_4255062
  have hstable : (prefixWord ++ tailWord_4255062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255062).length < 2 ^ (prefixWord ++ tailWord_4255062).sum := by decide
  have hdescent : baseEnd_4255062 < baseStart_4255062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255087 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 5, 2]
def baseStart_4255087 : Nat := 118140960795 + 4255087 * 2 ^ 59
def prefixEnd_4255087 : Nat := 4983230072969 + 3 ^ 40 * 4255087 * 2
def baseEnd_4255087 : Nat := 2184904857697898686243717

theorem tailTrace_4255087 : CollatzResearch.WordTrace tailWord_4255087 prefixEnd_4255087 2184904857697898686243717 := by
  unfold tailWord_4255087
  simp only [CollatzResearch.WordTrace]
  refine ⟨155195772735553984848291515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103463848490369323232194343 155195772735553984848291515)
  ·
    refine ⟨232793659103330977272437273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155195772735553984848291515 232793659103330977272437273)
    ·
      refine ⟨174595244327498232954327955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232793659103330977272437273 174595244327498232954327955)
      ·
        refine ⟨261892866491247349431491933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174595244327498232954327955 261892866491247349431491933)
        ·
          refine ⟨98209824934217756036809475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261892866491247349431491933 98209824934217756036809475)
          ·
            refine ⟨147314737401326634055214213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98209824934217756036809475 147314737401326634055214213)
            ·
              refine ⟨27621513262748743885352665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147314737401326634055214213 27621513262748743885352665)
              ·
                refine ⟨20716134947061557914014499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27621513262748743885352665 20716134947061557914014499)
                ·
                  refine ⟨31074202420592336871021749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20716134947061557914014499 31074202420592336871021749)
                  ·
                    refine ⟨2913206476930531581658289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31074202420592336871021749 2913206476930531581658289)
                    ·
                      refine ⟨2184904857697898686243717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913206476930531581658289 2184904857697898686243717)
                      ·
                        rfl

theorem cell23_4255087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5, 2].length) (baseStart_4255087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255087 prefixEnd_4255087 := by exact prefixLift 4255087
  have htrace : WordTrace (prefixWord ++ tailWord_4255087) baseStart_4255087 baseEnd_4255087 := by
    simpa [prefixWord, tailWord_4255087, baseEnd_4255087] using wordTrace_append hprefix tailTrace_4255087
  have hstable : (prefixWord ++ tailWord_4255087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255087).length < 2 ^ (prefixWord ++ tailWord_4255087).sum := by decide
  have hdescent : baseEnd_4255087 < baseStart_4255087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255090 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4255090 : Nat := 118140960795 + 4255090 * 2 ^ 59
def prefixEnd_4255090 : Nat := 4983230072969 + 3 ^ 40 * 4255090 * 2
def baseEnd_4255090 : Nat := 2184906398139862174506203

theorem tailTrace_4255090 : CollatzResearch.WordTrace tailWord_4255090 prefixEnd_4255090 2184906398139862174506203 := by
  unfold tailWord_4255090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38798970538635779090162681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103463921436362077573767149 38798970538635779090162681)
  ·
    refine ⟨29099227903976834317622011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38798970538635779090162681 29099227903976834317622011)
    ·
      refine ⟨43648841855965251476433017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29099227903976834317622011 43648841855965251476433017)
      ·
        refine ⟨32736631391973938607324763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43648841855965251476433017 32736631391973938607324763)
        ·
          refine ⟨49104947087960907910987145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32736631391973938607324763 49104947087960907910987145)
          ·
            refine ⟨36828710315970680933240359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49104947087960907910987145 36828710315970680933240359)
            ·
              refine ⟨55243065473956021399860539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36828710315970680933240359 55243065473956021399860539)
              ·
                refine ⟨82864598210934032099790809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55243065473956021399860539 82864598210934032099790809)
                ·
                  refine ⟨62148448658200524074843107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82864598210934032099790809 62148448658200524074843107)
                  ·
                    refine ⟨93222672987300786112264661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62148448658200524074843107 93222672987300786112264661)
                    ·
                      refine ⟨2184906398139862174506203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93222672987300786112264661 2184906398139862174506203)
                      ·
                        rfl

theorem cell23_4255090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4255090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255090 prefixEnd_4255090 := by exact prefixLift 4255090
  have htrace : WordTrace (prefixWord ++ tailWord_4255090) baseStart_4255090 baseEnd_4255090 := by
    simpa [prefixWord, tailWord_4255090, baseEnd_4255090] using wordTrace_append hprefix tailTrace_4255090
  have hstable : (prefixWord ++ tailWord_4255090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255090).length < 2 ^ (prefixWord ++ tailWord_4255090).sum := by decide
  have hdescent : baseEnd_4255090 < baseStart_4255090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255111 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_4255111 : Nat := 118140960795 + 4255111 * 2 ^ 59
def prefixEnd_4255111 : Nat := 4983230072969 + 3 ^ 40 * 4255111 * 2
def baseEnd_4255111 : Nat := 2184917181233606592343607

theorem tailTrace_4255111 : CollatzResearch.WordTrace tailWord_4255111 prefixEnd_4255111 2184917181233606592343607 := by
  unfold tailWord_4255111
  simp only [CollatzResearch.WordTrace]
  refine ⟨155196648087467036947165187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103464432058311357964776791 155196648087467036947165187)
  ·
    refine ⟨232794972131200555420747781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155196648087467036947165187 232794972131200555420747781)
    ·
      refine ⟨43649057274600104141390209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232794972131200555420747781 43649057274600104141390209)
      ·
        refine ⟨32736792955950078106042657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43649057274600104141390209 32736792955950078106042657)
        ·
          refine ⟨24552594716962558579531993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32736792955950078106042657 24552594716962558579531993)
          ·
            refine ⟨18414446037721918934648995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24552594716962558579531993 18414446037721918934648995)
            ·
              refine ⟨27621669056582878401973493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18414446037721918934648995 27621669056582878401973493)
              ·
                refine ⟨2589531474054644850185015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27621669056582878401973493 2589531474054644850185015)
                ·
                  refine ⟨3884297211081967275277523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589531474054644850185015 3884297211081967275277523)
                  ·
                    refine ⟨5826445816622950912916285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884297211081967275277523 5826445816622950912916285)
                    ·
                      refine ⟨2184917181233606592343607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826445816622950912916285 2184917181233606592343607)
                      ·
                        rfl

theorem cell23_4255111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_4255111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255111 prefixEnd_4255111 := by exact prefixLift 4255111
  have htrace : WordTrace (prefixWord ++ tailWord_4255111) baseStart_4255111 baseEnd_4255111 := by
    simpa [prefixWord, tailWord_4255111, baseEnd_4255111] using wordTrace_append hprefix tailTrace_4255111
  have hstable : (prefixWord ++ tailWord_4255111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255111).length < 2 ^ (prefixWord ++ tailWord_4255111).sum := by decide
  have hdescent : baseEnd_4255111 < baseStart_4255111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255140 : List Nat := [2, 3, 1, 2, 1, 1, 1, 12]
def baseStart_4255140 : Nat := 118140960795 + 4255140 * 2 ^ 59
def prefixEnd_4255140 : Nat := 4983230072969 + 3 ^ 40 * 4255140 * 2
def baseEnd_4255140 : Nat := 80923410080466184402999

theorem tailTrace_4255140 : CollatzResearch.WordTrace tailWord_4255140 prefixEnd_4255140 80923410080466184402999 := by
  unfold tailWord_4255140
  simp only [CollatzResearch.WordTrace]
  refine ⟨77598852902180987449985437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103465137202907983266647249 77598852902180987449985437)
  ·
    refine ⟨29099569838317870293744539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77598852902180987449985437 29099569838317870293744539)
    ·
      refine ⟨43649354757476805440616809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29099569838317870293744539 43649354757476805440616809)
      ·
        refine ⟨32737016068107604080462607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43649354757476805440616809 32737016068107604080462607)
        ·
          refine ⟨49105524102161406120693911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32737016068107604080462607 49105524102161406120693911)
          ·
            refine ⟨73658286153242109181040867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49105524102161406120693911 73658286153242109181040867)
            ·
              refine ⟨110487429229863163771561301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73658286153242109181040867 110487429229863163771561301)
              ·
                refine ⟨80923410080466184402999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 110487429229863163771561301 80923410080466184402999)
                ·
                  rfl

theorem cell23_4255140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 12].length) (baseStart_4255140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255140 prefixEnd_4255140 := by exact prefixLift 4255140
  have htrace : WordTrace (prefixWord ++ tailWord_4255140) baseStart_4255140 baseEnd_4255140 := by
    simpa [prefixWord, tailWord_4255140, baseEnd_4255140] using wordTrace_append hprefix tailTrace_4255140
  have hstable : (prefixWord ++ tailWord_4255140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255140).length < 2 ^ (prefixWord ++ tailWord_4255140).sum := by decide
  have hdescent : baseEnd_4255140 < baseStart_4255140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255157 : List Nat := [1, 3, 3, 2, 2, 2, 1, 9]
def baseStart_4255157 : Nat := 118140960795 + 4255157 * 2 ^ 59
def prefixEnd_4255157 : Nat := 4983230072969 + 3 ^ 40 * 4255157 * 2
def baseEnd_4255157 : Nat := 80923733383100496754385

theorem tailTrace_4255157 : CollatzResearch.WordTrace tailWord_4255157 prefixEnd_4255157 80923733383100496754385 := by
  unfold tailWord_4255157
  simp only [CollatzResearch.WordTrace]
  refine ⟨155198325845300386803339725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103465550563533591202226483 155198325845300386803339725)
  ·
    refine ⟨58199372191987645051252397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155198325845300386803339725 58199372191987645051252397)
    ·
      refine ⟨21824764571995366894219649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58199372191987645051252397 21824764571995366894219649)
      ·
        refine ⟨16368573428996525170664737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21824764571995366894219649 16368573428996525170664737)
        ·
          refine ⟨12276430071747393877998553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16368573428996525170664737 12276430071747393877998553)
          ·
            refine ⟨9207322553810545408498915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12276430071747393877998553 9207322553810545408498915)
            ·
              refine ⟨13810983830715818112748373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207322553810545408498915 13810983830715818112748373)
              ·
                refine ⟨80923733383100496754385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13810983830715818112748373 80923733383100496754385)
                ·
                  rfl

theorem cell23_4255157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 9].length) (baseStart_4255157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255157 prefixEnd_4255157 := by exact prefixLift 4255157
  have htrace : WordTrace (prefixWord ++ tailWord_4255157) baseStart_4255157 baseEnd_4255157 := by
    simpa [prefixWord, tailWord_4255157, baseEnd_4255157] using wordTrace_append hprefix tailTrace_4255157
  have hstable : (prefixWord ++ tailWord_4255157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255157).length < 2 ^ (prefixWord ++ tailWord_4255157).sum := by decide
  have hdescent : baseEnd_4255157 < baseStart_4255157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255167 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_4255167 : Nat := 118140960795 + 4255167 * 2 ^ 59
def prefixEnd_4255167 : Nat := 4983230072969 + 3 ^ 40 * 4255167 * 2
def baseEnd_4255167 : Nat := 2184945936150258373243349

theorem tailTrace_4255167 : CollatzResearch.WordTrace tailWord_4255167 prefixEnd_4255167 2184945936150258373243349 := by
  unfold tailWord_4255167
  simp only [CollatzResearch.WordTrace]
  refine ⟨155198690575264158511203755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103465793716842772340802503 155198690575264158511203755)
  ·
    refine ⟨232798035862896237766805633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155198690575264158511203755 232798035862896237766805633)
    ·
      refine ⟨174598526897172178325104225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232798035862896237766805633 174598526897172178325104225)
      ·
        refine ⟨130948895172879133743828169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174598526897172178325104225 130948895172879133743828169)
        ·
          refine ⟨98211671379659350307871127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130948895172879133743828169 98211671379659350307871127)
          ·
            refine ⟨147317507069489025461806691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98211671379659350307871127 147317507069489025461806691)
            ·
              refine ⟨220976260604233538192710037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147317507069489025461806691 220976260604233538192710037)
              ·
                refine ⟨10358262215823447102783283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220976260604233538192710037 10358262215823447102783283)
                ·
                  refine ⟨15537393323735170654174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10358262215823447102783283 15537393323735170654174925)
                  ·
                    refine ⟨5826522496400688995315597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15537393323735170654174925 5826522496400688995315597)
                    ·
                      refine ⟨2184945936150258373243349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826522496400688995315597 2184945936150258373243349)
                      ·
                        rfl

theorem cell23_4255167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_4255167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255167 prefixEnd_4255167 := by exact prefixLift 4255167
  have htrace : WordTrace (prefixWord ++ tailWord_4255167) baseStart_4255167 baseEnd_4255167 := by
    simpa [prefixWord, tailWord_4255167, baseEnd_4255167] using wordTrace_append hprefix tailTrace_4255167
  have hstable : (prefixWord ++ tailWord_4255167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255167).length < 2 ^ (prefixWord ++ tailWord_4255167).sum := by decide
  have hdescent : baseEnd_4255167 < baseStart_4255167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255168 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 1, 2, 2]
def baseStart_4255168 : Nat := 118140960795 + 4255168 * 2 ^ 59
def prefixEnd_4255168 : Nat := 4983230072969 + 3 ^ 40 * 4255168 * 2
def baseEnd_4255168 : Nat := 2184946449630912869330845

theorem tailTrace_4255168 : CollatzResearch.WordTrace tailWord_4255168 prefixEnd_4255168 2184946449630912869330845 := by
  unfold tailWord_4255168
  simp only [CollatzResearch.WordTrace]
  refine ⟨77599363524130267840995079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103465818032173690454660105 77599363524130267840995079)
  ·
    refine ⟨116399045286195401761492619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77599363524130267840995079 116399045286195401761492619)
    ·
      refine ⟨174598567929293102642238929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116399045286195401761492619 174598567929293102642238929)
      ·
        refine ⟨130948925946969826981679197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174598567929293102642238929 130948925946969826981679197)
        ·
          refine ⟨49105847230113685118129699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130948925946969826981679197 49105847230113685118129699)
          ·
            refine ⟨73658770845170527677194549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49105847230113685118129699 73658770845170527677194549)
            ·
              refine ⟨6905509766734736969736989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73658770845170527677194549 6905509766734736969736989)
              ·
                refine ⟨2589566162525526363651371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6905509766734736969736989 2589566162525526363651371)
                ·
                  refine ⟨3884349243788289545477057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589566162525526363651371 3884349243788289545477057)
                  ·
                    refine ⟨2913261932841217159107793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884349243788289545477057 2913261932841217159107793)
                    ·
                      refine ⟨2184946449630912869330845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913261932841217159107793 2184946449630912869330845)
                      ·
                        rfl

theorem cell23_4255168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_4255168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255168 prefixEnd_4255168 := by exact prefixLift 4255168
  have htrace : WordTrace (prefixWord ++ tailWord_4255168) baseStart_4255168 baseEnd_4255168 := by
    simpa [prefixWord, tailWord_4255168, baseEnd_4255168] using wordTrace_append hprefix tailTrace_4255168
  have hstable : (prefixWord ++ tailWord_4255168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255168).length < 2 ^ (prefixWord ++ tailWord_4255168).sum := by decide
  have hdescent : baseEnd_4255168 < baseStart_4255168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255201 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_4255201 : Nat := 118140960795 + 4255201 * 2 ^ 59
def prefixEnd_4255201 : Nat := 4983230072969 + 3 ^ 40 * 4255201 * 2
def baseEnd_4255201 : Nat := 2184963394492511240218193

theorem tailTrace_4255201 : CollatzResearch.WordTrace tailWord_4255201 prefixEnd_4255201 2184963394492511240218193 := by
  unfold tailWord_4255201
  simp only [CollatzResearch.WordTrace]
  refine ⟨155199930657140982317941457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103466620438093988211960971 155199930657140982317941457)
  ·
    refine ⟨116399947992855736738456093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155199930657140982317941457 116399947992855736738456093)
    ·
      refine ⟨43649980497320901276921035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116399947992855736738456093 43649980497320901276921035)
      ·
        refine ⟨65474970745981351915381553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43649980497320901276921035 65474970745981351915381553)
        ·
          refine ⟨49106228059486013936536165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65474970745981351915381553 49106228059486013936536165)
          ·
            refine ⟨9207417761153627613100531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49106228059486013936536165 9207417761153627613100531)
            ·
              refine ⟨13811126641730441419650797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207417761153627613100531 13811126641730441419650797)
              ·
                refine ⟨5179172490648915532369049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13811126641730441419650797 5179172490648915532369049)
                ·
                  refine ⟨3884379367986686649276787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179172490648915532369049 3884379367986686649276787)
                  ·
                    refine ⟨5826569051980029973915181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884379367986686649276787 5826569051980029973915181)
                    ·
                      refine ⟨2184963394492511240218193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826569051980029973915181 2184963394492511240218193)
                      ·
                        rfl

theorem cell23_4255201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_4255201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255201 prefixEnd_4255201 := by exact prefixLift 4255201
  have htrace : WordTrace (prefixWord ++ tailWord_4255201) baseStart_4255201 baseEnd_4255201 := by
    simpa [prefixWord, tailWord_4255201, baseEnd_4255201] using wordTrace_append hprefix tailTrace_4255201
  have hstable : (prefixWord ++ tailWord_4255201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255201).length < 2 ^ (prefixWord ++ tailWord_4255201).sum := by decide
  have hdescent : baseEnd_4255201 < baseStart_4255201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255224 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_4255224 : Nat := 118140960795 + 4255224 * 2 ^ 59
def prefixEnd_4255224 : Nat := 4983230072969 + 3 ^ 40 * 4255224 * 2
def baseEnd_4255224 : Nat := 2184975204547564650230587

theorem tailTrace_4255224 : CollatzResearch.WordTrace tailWord_4255224 prefixEnd_4255224 2184975204547564650230587 := by
  unfold tailWord_4255224
  simp only [CollatzResearch.WordTrace]
  refine ⟨77600384768028828623014363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103467179690705104830685817 77600384768028828623014363)
  ·
    refine ⟨116400577152043242934521545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77600384768028828623014363 116400577152043242934521545)
    ·
      refine ⟨87300432864032432200891159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116400577152043242934521545 87300432864032432200891159)
      ·
        refine ⟨130950649296048648301336739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87300432864032432200891159 130950649296048648301336739)
        ·
          refine ⟨196425973944072972452005109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130950649296048648301336739 196425973944072972452005109)
          ·
            refine ⟨18414935057256841167375479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196425973944072972452005109 18414935057256841167375479)
            ·
              refine ⟨27622402585885261751063219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18414935057256841167375479 27622402585885261751063219)
              ·
                refine ⟨41433603878827892626594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27622402585885261751063219 41433603878827892626594829)
                ·
                  refine ⟨15537601454560459734973061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41433603878827892626594829 15537601454560459734973061)
                  ·
                    refine ⟨2913300272730086200307449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15537601454560459734973061 2913300272730086200307449)
                    ·
                      refine ⟨2184975204547564650230587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913300272730086200307449 2184975204547564650230587)
                      ·
                        rfl

theorem cell23_4255224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_4255224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255224 prefixEnd_4255224 := by exact prefixLift 4255224
  have htrace : WordTrace (prefixWord ++ tailWord_4255224) baseStart_4255224 baseEnd_4255224 := by
    simpa [prefixWord, tailWord_4255224, baseEnd_4255224] using wordTrace_append hprefix tailTrace_4255224
  have hstable : (prefixWord ++ tailWord_4255224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255224).length < 2 ^ (prefixWord ++ tailWord_4255224).sum := by decide
  have hdescent : baseEnd_4255224 < baseStart_4255224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255237 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_4255237 : Nat := 118140960795 + 4255237 * 2 ^ 59
def prefixEnd_4255237 : Nat := 4983230072969 + 3 ^ 40 * 4255237 * 2
def baseEnd_4255237 : Nat := 2184981879796073099368027

theorem tailTrace_4255237 : CollatzResearch.WordTrace tailWord_4255237 prefixEnd_4255237 2184981879796073099368027 := by
  unfold tailWord_4255237
  simp only [CollatzResearch.WordTrace]
  refine ⟨155201243685010560466251965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103467495790007040310834643 155201243685010560466251965)
  ·
    refine ⟨58200466381878960174844487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155201243685010560466251965 58200466381878960174844487)
    ·
      refine ⟨87300699572818440262266731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58200466381878960174844487 87300699572818440262266731)
      ·
        refine ⟨130951049359227660393400097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87300699572818440262266731 130951049359227660393400097)
        ·
          refine ⟨98213287019420745295050073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130951049359227660393400097 98213287019420745295050073)
          ·
            refine ⟨73659965264565558971287555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98213287019420745295050073 73659965264565558971287555)
            ·
              refine ⟨110489947896848338456931333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73659965264565558971287555 110489947896848338456931333)
              ·
                refine ⟨20716865230659063460674625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110489947896848338456931333 20716865230659063460674625)
                ·
                  refine ⟨15537648922994297595505969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20716865230659063460674625 15537648922994297595505969)
                  ·
                    refine ⟨11653236692245723196629477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15537648922994297595505969 11653236692245723196629477)
                    ·
                      refine ⟨2184981879796073099368027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11653236692245723196629477 2184981879796073099368027)
                      ·
                        rfl

theorem cell23_4255237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_4255237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255237 prefixEnd_4255237 := by exact prefixLift 4255237
  have htrace : WordTrace (prefixWord ++ tailWord_4255237) baseStart_4255237 baseEnd_4255237 := by
    simpa [prefixWord, tailWord_4255237, baseEnd_4255237] using wordTrace_append hprefix tailTrace_4255237
  have hstable : (prefixWord ++ tailWord_4255237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255237).length < 2 ^ (prefixWord ++ tailWord_4255237).sum := by decide
  have hdescent : baseEnd_4255237 < baseStart_4255237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255264 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 7]
def baseStart_4255264 : Nat := 118140960795 + 4255264 * 2 ^ 59
def prefixEnd_4255264 : Nat := 4983230072969 + 3 ^ 40 * 4255264 * 2
def baseEnd_4255264 : Nat := 242777304863749388192267

theorem tailTrace_4255264 : CollatzResearch.WordTrace tailWord_4255264 prefixEnd_4255264 242777304863749388192267 := by
  unfold tailWord_4255264
  simp only [CollatzResearch.WordTrace]
  refine ⟨77601114227956372038742423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103468152303941829384989897 77601114227956372038742423)
  ·
    refine ⟨116401671341934558058113635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77601114227956372038742423 116401671341934558058113635)
    ·
      refine ⟨174602507012901837087170453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116401671341934558058113635 174602507012901837087170453)
      ·
        refine ⟨8184492516229773613461115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174602507012901837087170453 8184492516229773613461115)
        ·
          refine ⟨12276738774344660420191673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8184492516229773613461115 12276738774344660420191673)
          ·
            refine ⟨9207554080758495315143755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12276738774344660420191673 9207554080758495315143755)
            ·
              refine ⟨13811331121137742972715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207554080758495315143755 13811331121137742972715633)
              ·
                refine ⟨10358498340853307229536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13811331121137742972715633 10358498340853307229536725)
                ·
                  refine ⟨242777304863749388192267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10358498340853307229536725 242777304863749388192267)
                  ·
                    rfl

theorem cell23_4255264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_4255264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255264 prefixEnd_4255264 := by exact prefixLift 4255264
  have htrace : WordTrace (prefixWord ++ tailWord_4255264) baseStart_4255264 baseEnd_4255264 := by
    simpa [prefixWord, tailWord_4255264, baseEnd_4255264] using wordTrace_append hprefix tailTrace_4255264
  have hstable : (prefixWord ++ tailWord_4255264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255264).length < 2 ^ (prefixWord ++ tailWord_4255264).sum := by decide
  have hdescent : baseEnd_4255264 < baseStart_4255264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255274 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4255274 : Nat := 118140960795 + 4255274 * 2 ^ 59
def prefixEnd_4255274 : Nat := 4983230072969 + 3 ^ 40 * 4255274 * 2
def baseEnd_4255274 : Nat := 2185000878580289454605357

theorem tailTrace_4255274 : CollatzResearch.WordTrace tailWord_4255274 prefixEnd_4255274 2185000878580289454605357 := by
  unfold tailWord_4255274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38800648296469128946337219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103468395457251010523565917 38800648296469128946337219)
  ·
    refine ⟨58200972444703693419505829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38800648296469128946337219 58200972444703693419505829)
    ·
      refine ⟨10912682333381942516157343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58200972444703693419505829 10912682333381942516157343)
      ·
        refine ⟨16369023500072913774236015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10912682333381942516157343 16369023500072913774236015)
        ·
          refine ⟨24553535250109370661354023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16369023500072913774236015 24553535250109370661354023)
          ·
            refine ⟨36830302875164055992031035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24553535250109370661354023 36830302875164055992031035)
            ·
              refine ⟨55245454312746083988046553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36830302875164055992031035 55245454312746083988046553)
              ·
                refine ⟨41434090734559562991034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55245454312746083988046553 41434090734559562991034915)
                ·
                  refine ⟨62151136101839344486552373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41434090734559562991034915 62151136101839344486552373)
                  ·
                    refine ⟨5826669009547438545614285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62151136101839344486552373 5826669009547438545614285)
                    ·
                      refine ⟨2185000878580289454605357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826669009547438545614285 2185000878580289454605357)
                      ·
                        rfl

theorem cell23_4255274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4255274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255274 prefixEnd_4255274 := by exact prefixLift 4255274
  have htrace : WordTrace (prefixWord ++ tailWord_4255274) baseStart_4255274 baseEnd_4255274 := by
    simpa [prefixWord, tailWord_4255274, baseEnd_4255274] using wordTrace_append hprefix tailTrace_4255274
  have hstable : (prefixWord ++ tailWord_4255274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255274).length < 2 ^ (prefixWord ++ tailWord_4255274).sum := by decide
  have hdescent : baseEnd_4255274 < baseStart_4255274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255292 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_4255292 : Nat := 118140960795 + 4255292 * 2 ^ 59
def prefixEnd_4255292 : Nat := 4983230072969 + 3 ^ 40 * 4255292 * 2
def baseEnd_4255292 : Nat := 2185010121232070384180275

theorem tailTrace_4255292 : CollatzResearch.WordTrace tailWord_4255292 prefixEnd_4255292 2185010121232070384180275 := by
  unfold tailWord_4255292
  simp only [CollatzResearch.WordTrace]
  refine ⟨77601624849905652429752065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103468833133207536573002753 77601624849905652429752065)
  ·
    refine ⟨58201218637429239322314049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77601624849905652429752065 58201218637429239322314049)
    ·
      refine ⟨43650913978071929491735537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58201218637429239322314049 43650913978071929491735537)
      ·
        refine ⟨32738185483553947118801653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43650913978071929491735537 32738185483553947118801653)
        ·
          refine ⟨3069204889083182542387655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32738185483553947118801653 3069204889083182542387655)
          ·
            refine ⟨4603807333624773813581483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069204889083182542387655 4603807333624773813581483)
            ·
              refine ⟨6905711000437160720372225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603807333624773813581483 6905711000437160720372225)
              ·
                refine ⟨5179283250327870540279169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6905711000437160720372225 5179283250327870540279169)
                ·
                  refine ⟨3884462437745902905209377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179283250327870540279169 3884462437745902905209377)
                  ·
                    refine ⟨2913346828309427178907033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884462437745902905209377 2913346828309427178907033)
                    ·
                      refine ⟨2185010121232070384180275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913346828309427178907033 2185010121232070384180275)
                      ·
                        rfl

theorem cell23_4255292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_4255292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255292 prefixEnd_4255292 := by exact prefixLift 4255292
  have htrace : WordTrace (prefixWord ++ tailWord_4255292) baseStart_4255292 baseEnd_4255292 := by
    simpa [prefixWord, tailWord_4255292, baseEnd_4255292] using wordTrace_append hprefix tailTrace_4255292
  have hstable : (prefixWord ++ tailWord_4255292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255292).length < 2 ^ (prefixWord ++ tailWord_4255292).sum := by decide
  have hdescent : baseEnd_4255292 < baseStart_4255292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255314 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4255314 : Nat := 118140960795 + 4255314 * 2 ^ 59
def prefixEnd_4255314 : Nat := 4983230072969 + 3 ^ 40 * 4255314 * 2
def baseEnd_4255314 : Nat := 2185021417806469298105173

theorem tailTrace_4255314 : CollatzResearch.WordTrace tailWord_4255314 prefixEnd_4255314 2185021417806469298105173 := by
  unfold tailWord_4255314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38801013026432900654201249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103469368070487735077869997 38801013026432900654201249)
  ·
    refine ⟨29100759769824675490650937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38801013026432900654201249 29100759769824675490650937)
    ·
      refine ⟨21825569827368506617988203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29100759769824675490650937 21825569827368506617988203)
      ·
        refine ⟨32738354741052759926982305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21825569827368506617988203 32738354741052759926982305)
        ·
          refine ⟨24553766055789569945236729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32738354741052759926982305 24553766055789569945236729)
          ·
            refine ⟨18415324541842177458927547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24553766055789569945236729 18415324541842177458927547)
            ·
              refine ⟨27622986812763266188391321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18415324541842177458927547 27622986812763266188391321)
              ·
                refine ⟨20717240109572449641293491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27622986812763266188391321 20717240109572449641293491)
                ·
                  refine ⟨31075860164358674461940237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20717240109572449641293491 31075860164358674461940237)
                  ·
                    refine ⟨11653447561634502923227589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31075860164358674461940237 11653447561634502923227589)
                    ·
                      refine ⟨2185021417806469298105173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11653447561634502923227589 2185021417806469298105173)
                      ·
                        rfl

theorem cell23_4255314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4255314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255314 prefixEnd_4255314 := by exact prefixLift 4255314
  have htrace : WordTrace (prefixWord ++ tailWord_4255314) baseStart_4255314 baseEnd_4255314 := by
    simpa [prefixWord, tailWord_4255314, baseEnd_4255314] using wordTrace_append hprefix tailTrace_4255314
  have hstable : (prefixWord ++ tailWord_4255314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255314).length < 2 ^ (prefixWord ++ tailWord_4255314).sum := by decide
  have hdescent : baseEnd_4255314 < baseStart_4255314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255337 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 8]
def baseStart_4255337 : Nat := 118140960795 + 4255337 * 2 ^ 59
def prefixEnd_4255337 : Nat := 4983230072969 + 3 ^ 40 * 4255337 * 2
def baseEnd_4255337 : Nat := 242781469762391412013063

theorem tailTrace_4255337 : CollatzResearch.WordTrace tailWord_4255337 prefixEnd_4255337 242781469762391412013063 := by
  unfold tailWord_4255337
  simp only [CollatzResearch.WordTrace]
  refine ⟨155204890984648277544892265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103469927323098851696594843 155204890984648277544892265)
  ·
    refine ⟨116403668238486208158669199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155204890984648277544892265 116403668238486208158669199)
    ·
      refine ⟨174605502357729312238003799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116403668238486208158669199 174605502357729312238003799)
      ·
        refine ⟨261908253536593968357005699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174605502357729312238003799 261908253536593968357005699)
        ·
          refine ⟨392862380304890952535508549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261908253536593968357005699 392862380304890952535508549)
          ·
            refine ⟨73661696307167053600407853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 392862380304890952535508549 73661696307167053600407853)
            ·
              refine ⟨27623136115187645100152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73661696307167053600407853 27623136115187645100152945)
              ·
                refine ⟨20717352086390733825114709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27623136115187645100152945 20717352086390733825114709)
                ·
                  refine ⟨242781469762391412013063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20717352086390733825114709 242781469762391412013063)
                  ·
                    rfl

theorem cell23_4255337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_4255337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255337 prefixEnd_4255337 := by exact prefixLift 4255337
  have htrace : WordTrace (prefixWord ++ tailWord_4255337) baseStart_4255337 baseEnd_4255337 := by
    simpa [prefixWord, tailWord_4255337, baseEnd_4255337] using wordTrace_append hprefix tailTrace_4255337
  have hstable : (prefixWord ++ tailWord_4255337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255337).length < 2 ^ (prefixWord ++ tailWord_4255337).sum := by decide
  have hdescent : baseEnd_4255337 < baseStart_4255337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255377 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_4255377 : Nat := 118140960795 + 4255377 * 2 ^ 59
def prefixEnd_4255377 : Nat := 4983230072969 + 3 ^ 40 * 4255377 * 2
def baseEnd_4255377 : Nat := 2185053767087702551617383

theorem tailTrace_4255377 : CollatzResearch.WordTrace tailWord_4255377 prefixEnd_4255377 2185053767087702551617383 := by
  unfold tailWord_4255377
  simp only [CollatzResearch.WordTrace]
  refine ⟨155206349904503364376348385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103470899936335576250898923 155206349904503364376348385)
  ·
    refine ⟨116404762428377523282261289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155206349904503364376348385 116404762428377523282261289)
    ·
      refine ⟨87303571821283142461695967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116404762428377523282261289 87303571821283142461695967)
      ·
        refine ⟨130955357731924713692543951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87303571821283142461695967 130955357731924713692543951)
        ·
          refine ⟨196433036597887070538815927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130955357731924713692543951 196433036597887070538815927)
          ·
            refine ⟨294649554896830605808223891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196433036597887070538815927 294649554896830605808223891)
            ·
              refine ⟨441974332345245908712335837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294649554896830605808223891 441974332345245908712335837)
              ·
                refine ⟨165740374629467215767125939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441974332345245908712335837 165740374629467215767125939)
                ·
                  refine ⟨248610561944200823650688909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165740374629467215767125939 248610561944200823650688909)
                  ·
                    refine ⟨93228960729075308869008341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248610561944200823650688909 93228960729075308869008341)
                    ·
                      refine ⟨2185053767087702551617383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93228960729075308869008341 2185053767087702551617383)
                      ·
                        rfl

theorem cell23_4255377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_4255377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255377 prefixEnd_4255377 := by exact prefixLift 4255377
  have htrace : WordTrace (prefixWord ++ tailWord_4255377) baseStart_4255377 baseEnd_4255377 := by
    simpa [prefixWord, tailWord_4255377, baseEnd_4255377] using wordTrace_append hprefix tailTrace_4255377
  have hstable : (prefixWord ++ tailWord_4255377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255377).length < 2 ^ (prefixWord ++ tailWord_4255377).sum := by decide
  have hdescent : baseEnd_4255377 < baseStart_4255377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255381 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_4255381 : Nat := 118140960795 + 4255381 * 2 ^ 59
def prefixEnd_4255381 : Nat := 4983230072969 + 3 ^ 40 * 4255381 * 2
def baseEnd_4255381 : Nat := 2185055821010320535967365

theorem tailTrace_4255381 : CollatzResearch.WordTrace tailWord_4255381 prefixEnd_4255381 2185055821010320535967365 := by
  unfold tailWord_4255381
  simp only [CollatzResearch.WordTrace]
  refine ⟨155206495796488873059493997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103470997197659248706329331 155206495796488873059493997)
  ·
    refine ⟨58202435923683327397310249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155206495796488873059493997 58202435923683327397310249)
    ·
      refine ⟨43651826942762495547982687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58202435923683327397310249 43651826942762495547982687)
      ·
        refine ⟨65477740414143743321974031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43651826942762495547982687 65477740414143743321974031)
        ·
          refine ⟨98216610621215614982961047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65477740414143743321974031 98216610621215614982961047)
          ·
            refine ⟨147324915931823422474441571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98216610621215614982961047 147324915931823422474441571)
            ·
              refine ⟨220987373897735133711662357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147324915931823422474441571 220987373897735133711662357)
              ·
                refine ⟨10358783151456334392734173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220987373897735133711662357 10358783151456334392734173)
                ·
                  refine ⟨3884543681796125397275315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10358783151456334392734173 3884543681796125397275315)
                  ·
                    refine ⟨5826815522694188095912973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884543681796125397275315 5826815522694188095912973)
                    ·
                      refine ⟨2185055821010320535967365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826815522694188095912973 2185055821010320535967365)
                      ·
                        rfl

theorem cell23_4255381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_4255381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255381 prefixEnd_4255381 := by exact prefixLift 4255381
  have htrace : WordTrace (prefixWord ++ tailWord_4255381) baseStart_4255381 baseEnd_4255381 := by
    simpa [prefixWord, tailWord_4255381, baseEnd_4255381] using wordTrace_append hprefix tailTrace_4255381
  have hstable : (prefixWord ++ tailWord_4255381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255381).length < 2 ^ (prefixWord ++ tailWord_4255381).sum := by decide
  have hdescent : baseEnd_4255381 < baseStart_4255381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255415 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_4255415 : Nat := 118140960795 + 4255415 * 2 ^ 59
def prefixEnd_4255415 : Nat := 4983230072969 + 3 ^ 40 * 4255415 * 2
def baseEnd_4255415 : Nat := 2185073279352573402942209

theorem tailTrace_4255415 : CollatzResearch.WordTrace tailWord_4255415 prefixEnd_4255415 2185073279352573402942209 := by
  unfold tailWord_4255415
  simp only [CollatzResearch.WordTrace]
  refine ⟨155207735878365696866231699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103471823918910464577487799 155207735878365696866231699)
  ·
    refine ⟨232811603817548545299347549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155207735878365696866231699 232811603817548545299347549)
    ·
      refine ⟨87304351431580704487255331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232811603817548545299347549 87304351431580704487255331)
      ·
        refine ⟨130956527147371056730882997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87304351431580704487255331 130956527147371056730882997)
        ·
          refine ⟨12277174420066036568520281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130956527147371056730882997 12277174420066036568520281)
          ·
            refine ⟨9207880815049527426390211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12277174420066036568520281 9207880815049527426390211)
            ·
              refine ⟨13811821222574291139585317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207880815049527426390211 13811821222574291139585317)
              ·
                refine ⟨2589716479232679588672247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13811821222574291139585317 2589716479232679588672247)
                ·
                  refine ⟨3884574718849019383008371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589716479232679588672247 3884574718849019383008371)
                  ·
                    refine ⟨5826862078273529074512557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884574718849019383008371 5826862078273529074512557)
                    ·
                      refine ⟨2185073279352573402942209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826862078273529074512557 2185073279352573402942209)
                      ·
                        rfl

theorem cell23_4255415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_4255415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255415 prefixEnd_4255415 := by exact prefixLift 4255415
  have htrace : WordTrace (prefixWord ++ tailWord_4255415) baseStart_4255415 baseEnd_4255415 := by
    simpa [prefixWord, tailWord_4255415, baseEnd_4255415] using wordTrace_append hprefix tailTrace_4255415
  have hstable : (prefixWord ++ tailWord_4255415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255415).length < 2 ^ (prefixWord ++ tailWord_4255415).sum := by decide
  have hdescent : baseEnd_4255415 < baseStart_4255415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255424 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_4255424 : Nat := 118140960795 + 4255424 * 2 ^ 59
def prefixEnd_4255424 : Nat := 4983230072969 + 3 ^ 40 * 4255424 * 2
def baseEnd_4255424 : Nat := 2185077900678463867729667

theorem tailTrace_4255424 : CollatzResearch.WordTrace tailWord_4255424 prefixEnd_4255424 2185077900678463867729667 := by
  unfold tailWord_4255424
  simp only [CollatzResearch.WordTrace]
  refine ⟨77604032067666545701654663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103472042756888727602206217 77604032067666545701654663)
  ·
    refine ⟨116406048101499818552481995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77604032067666545701654663 116406048101499818552481995)
    ·
      refine ⟨174609072152249727828722993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116406048101499818552481995 174609072152249727828722993)
      ·
        refine ⟨130956804114187295871542245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174609072152249727828722993 130956804114187295871542245)
        ·
          refine ⟨24554400771410117975914171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130956804114187295871542245 24554400771410117975914171)
          ·
            refine ⟨36831601157115176963871257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24554400771410117975914171 36831601157115176963871257)
            ·
              refine ⟨27623700867836382722903443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36831601157115176963871257 27623700867836382722903443)
              ·
                refine ⟨41435551301754574084355165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27623700867836382722903443 41435551301754574084355165)
                ·
                  refine ⟨15538331738157965281633187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41435551301754574084355165 15538331738157965281633187)
                  ·
                    refine ⟨23307497607236947922449781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15538331738157965281633187 23307497607236947922449781)
                    ·
                      refine ⟨2185077900678463867729667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23307497607236947922449781 2185077900678463867729667)
                      ·
                        rfl

theorem cell23_4255424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_4255424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255424 prefixEnd_4255424 := by exact prefixLift 4255424
  have htrace : WordTrace (prefixWord ++ tailWord_4255424) baseStart_4255424 baseEnd_4255424 := by
    simpa [prefixWord, tailWord_4255424, baseEnd_4255424] using wordTrace_append hprefix tailTrace_4255424
  have hstable : (prefixWord ++ tailWord_4255424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255424).length < 2 ^ (prefixWord ++ tailWord_4255424).sum := by decide
  have hdescent : baseEnd_4255424 < baseStart_4255424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255431 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 2, 4]
def baseStart_4255431 : Nat := 118140960795 + 4255431 * 2 ^ 59
def prefixEnd_4255431 : Nat := 4983230072969 + 3 ^ 40 * 4255431 * 2
def baseEnd_4255431 : Nat := 728360498347681780114045

theorem tailTrace_4255431 : CollatzResearch.WordTrace tailWord_4255431 prefixEnd_4255431 728360498347681780114045 := by
  unfold tailWord_4255431
  simp only [CollatzResearch.WordTrace]
  refine ⟨155208319446307731598814147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103472212964205154399209431 155208319446307731598814147)
  ·
    refine ⟨232812479169461597398221221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155208319446307731598814147 232812479169461597398221221)
    ·
      refine ⟨43652339844274049512166479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232812479169461597398221221 43652339844274049512166479)
      ·
        refine ⟨65478509766411074268249719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43652339844274049512166479 65478509766411074268249719)
        ·
          refine ⟨98217764649616611402374579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65478509766411074268249719 98217764649616611402374579)
          ·
            refine ⟨147326646974424917103561869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98217764649616611402374579 147326646974424917103561869)
            ·
              refine ⟨55247492615409343913835701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147326646974424917103561869 55247492615409343913835701)
              ·
                refine ⟨5179452432694625991922097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55247492615409343913835701 5179452432694625991922097)
                ·
                  refine ⟨3884589324520969493941573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179452432694625991922097 3884589324520969493941573)
                  ·
                    refine ⟨728360498347681780114045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3884589324520969493941573 728360498347681780114045)
                    ·
                      rfl

theorem cell23_4255431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_4255431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255431 prefixEnd_4255431 := by exact prefixLift 4255431
  have htrace : WordTrace (prefixWord ++ tailWord_4255431) baseStart_4255431 baseEnd_4255431 := by
    simpa [prefixWord, tailWord_4255431, baseEnd_4255431] using wordTrace_append hprefix tailTrace_4255431
  have hstable : (prefixWord ++ tailWord_4255431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255431).length < 2 ^ (prefixWord ++ tailWord_4255431).sum := by decide
  have hdescent : baseEnd_4255431 < baseStart_4255431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255441 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_4255441 : Nat := 118140960795 + 4255441 * 2 ^ 59
def prefixEnd_4255441 : Nat := 4983230072969 + 3 ^ 40 * 4255441 * 2
def baseEnd_4255441 : Nat := 2185086629849590301217089

theorem tailTrace_4255441 : CollatzResearch.WordTrace tailWord_4255441 prefixEnd_4255441 2185086629849590301217089 := by
  unfold tailWord_4255441
  simp only [CollatzResearch.WordTrace]
  refine ⟨155208684176271503306678177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103472456117514335537785451 155208684176271503306678177)
  ·
    refine ⟨116406513132203627480008633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155208684176271503306678177 116406513132203627480008633)
    ·
      refine ⟨87304884849152720610006475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116406513132203627480008633 87304884849152720610006475)
      ·
        refine ⟨130957327273729080915009713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87304884849152720610006475 130957327273729080915009713)
        ·
          refine ⟨98217995455296810686257285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130957327273729080915009713 98217995455296810686257285)
          ·
            refine ⟨18415874147868152003673241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98217995455296810686257285 18415874147868152003673241)
            ·
              refine ⟨13811905610901114002754931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18415874147868152003673241 13811905610901114002754931)
              ·
                refine ⟨20717858416351671004132397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13811905610901114002754931 20717858416351671004132397)
                ·
                  refine ⟨7769196906131876626549649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20717858416351671004132397 7769196906131876626549649)
                  ·
                    refine ⟨5826897679598907469912237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7769196906131876626549649 5826897679598907469912237)
                    ·
                      refine ⟨2185086629849590301217089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5826897679598907469912237 2185086629849590301217089)
                      ·
                        rfl

theorem cell23_4255441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_4255441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255441 prefixEnd_4255441 := by exact prefixLift 4255441
  have htrace : WordTrace (prefixWord ++ tailWord_4255441) baseStart_4255441 baseEnd_4255441 := by
    simpa [prefixWord, tailWord_4255441, baseEnd_4255441] using wordTrace_append hprefix tailTrace_4255441
  have hstable : (prefixWord ++ tailWord_4255441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255441).length < 2 ^ (prefixWord ++ tailWord_4255441).sum := by decide
  have hdescent : baseEnd_4255441 < baseStart_4255441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255452 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4255452 : Nat := 118140960795 + 4255452 * 2 ^ 59
def prefixEnd_4255452 : Nat := 4983230072969 + 3 ^ 40 * 4255452 * 2
def baseEnd_4255452 : Nat := 728364092712263252726513

theorem tailTrace_4255452 : CollatzResearch.WordTrace tailWord_4255452 prefixEnd_4255452 728364092712263252726513 := by
  unfold tailWord_4255452
  simp only [CollatzResearch.WordTrace]
  refine ⟨77604542689615826092664305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103472723586154434790219073 77604542689615826092664305)
  ·
    refine ⟨58203407017211869569498229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77604542689615826092664305 58203407017211869569498229)
    ·
      refine ⟨5456569407863612772140459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58203407017211869569498229 5456569407863612772140459)
      ·
        refine ⟨8184854111795419158210689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456569407863612772140459 8184854111795419158210689)
        ·
          refine ⟨6138640583846564368658017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8184854111795419158210689 6138640583846564368658017)
          ·
            refine ⟨4603980437884923276493513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6138640583846564368658017 4603980437884923276493513)
            ·
              refine ⟨3452985328413692457370135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603980437884923276493513 3452985328413692457370135)
              ·
                refine ⟨5179477992620538686055203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452985328413692457370135 5179477992620538686055203)
                ·
                  refine ⟨7769216988930808029082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5179477992620538686055203 7769216988930808029082805)
                  ·
                    refine ⟨728364092712263252726513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7769216988930808029082805 728364092712263252726513)
                    ·
                      rfl

theorem cell23_4255452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4255452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255452 prefixEnd_4255452 := by exact prefixLift 4255452
  have htrace : WordTrace (prefixWord ++ tailWord_4255452) baseStart_4255452 baseEnd_4255452 := by
    simpa [prefixWord, tailWord_4255452, baseEnd_4255452] using wordTrace_append hprefix tailTrace_4255452
  have hstable : (prefixWord ++ tailWord_4255452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255452).length < 2 ^ (prefixWord ++ tailWord_4255452).sum := by decide
  have hdescent : baseEnd_4255452 < baseStart_4255452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255495 : List Nat := [1, 1, 4, 4, 3, 1, 2, 7]
def baseStart_4255495 : Nat := 118140960795 + 4255495 * 2 ^ 59
def prefixEnd_4255495 : Nat := 4983230072969 + 3 ^ 40 * 4255495 * 2
def baseEnd_4255495 : Nat := 80930161400182707034883

theorem tailTrace_4255495 : CollatzResearch.WordTrace tailWord_4255495 prefixEnd_4255495 80930161400182707034883 := by
  unfold tailWord_4255495
  simp only [CollatzResearch.WordTrace]
  refine ⟨155210653718075870529143939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103473769145383913686095959 155210653718075870529143939)
  ·
    refine ⟨232815980577113805793715909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155210653718075870529143939 232815980577113805793715909)
    ·
      refine ⟨43652996358208838586321733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232815980577113805793715909 43652996358208838586321733)
      ·
        refine ⟨8184936817164157234935325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43652996358208838586321733 8184936817164157234935325)
        ·
          refine ⟨3069351306436558963100747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8184936817164157234935325 3069351306436558963100747)
          ·
            refine ⟨4604026959654838444651121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069351306436558963100747 4604026959654838444651121)
            ·
              refine ⟨3453020219741128833488341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4604026959654838444651121 3453020219741128833488341)
              ·
                refine ⟨80930161400182707034883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3453020219741128833488341 80930161400182707034883)
                ·
                  rfl

theorem cell23_4255495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 7].length) (baseStart_4255495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255495 prefixEnd_4255495 := by exact prefixLift 4255495
  have htrace : WordTrace (prefixWord ++ tailWord_4255495) baseStart_4255495 baseEnd_4255495 := by
    simpa [prefixWord, tailWord_4255495, baseEnd_4255495] using wordTrace_append hprefix tailTrace_4255495
  have hstable : (prefixWord ++ tailWord_4255495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255495).length < 2 ^ (prefixWord ++ tailWord_4255495).sum := by decide
  have hdescent : baseEnd_4255495 < baseStart_4255495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255506 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4255506 : Nat := 118140960795 + 4255506 * 2 ^ 59
def prefixEnd_4255506 : Nat := 4983230072969 + 3 ^ 40 * 4255506 * 2
def baseEnd_4255506 : Nat := 2185120006092132546904291

theorem tailTrace_4255506 : CollatzResearch.WordTrace tailWord_4255506 prefixEnd_4255506 2185120006092132546904291 := by
  unfold tailWord_4255506
  simp only [CollatzResearch.WordTrace]
  refine ⟨38802763730259004851948593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103474036614024012938529581 38802763730259004851948593)
  ·
    refine ⟨29102072797694253638961445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38802763730259004851948593 29102072797694253638961445)
    ·
      refine ⟨5456638649567672557305271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29102072797694253638961445 5456638649567672557305271)
      ·
        refine ⟨8184957974351508835957907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456638649567672557305271 8184957974351508835957907)
        ·
          refine ⟨12277436961527263253936861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8184957974351508835957907 12277436961527263253936861)
          ·
            refine ⟨4604038860572723720226323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12277436961527263253936861 4604038860572723720226323)
            ·
              refine ⟨6906058290859085580339485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604038860572723720226323 6906058290859085580339485)
              ·
                refine ⟨2589771859072157092627307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6906058290859085580339485 2589771859072157092627307)
                ·
                  refine ⟨3884657788608235638940961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589771859072157092627307 3884657788608235638940961)
                  ·
                    refine ⟨2913493341456176729205721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884657788608235638940961 2913493341456176729205721)
                    ·
                      refine ⟨2185120006092132546904291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913493341456176729205721 2185120006092132546904291)
                      ·
                        rfl

theorem cell23_4255506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4255506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255506 prefixEnd_4255506 := by exact prefixLift 4255506
  have htrace : WordTrace (prefixWord ++ tailWord_4255506) baseStart_4255506 baseEnd_4255506 := by
    simpa [prefixWord, tailWord_4255506, baseEnd_4255506] using wordTrace_append hprefix tailTrace_4255506
  have hstable : (prefixWord ++ tailWord_4255506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255506).length < 2 ^ (prefixWord ++ tailWord_4255506).sum := by decide
  have hdescent : baseEnd_4255506 < baseStart_4255506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255539 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 2, 1, 3]
def baseStart_4255539 : Nat := 118140960795 + 4255539 * 2 ^ 59
def prefixEnd_4255539 : Nat := 4983230072969 + 3 ^ 40 * 4255539 * 2
def baseEnd_4255539 : Nat := 2185136950953730917791639

theorem tailTrace_4255539 : CollatzResearch.WordTrace tailWord_4255539 prefixEnd_4255539 2185136950953730917791639 := by
  unfold tailWord_4255539
  simp only [CollatzResearch.WordTrace]
  refine ⟨155212258529916466043745671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103474839019944310695830447 155212258529916466043745671)
  ·
    refine ⟨232818387794874699065618507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155212258529916466043745671 232818387794874699065618507)
    ·
      refine ⟨349227581692312048598427761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232818387794874699065618507 349227581692312048598427761)
      ·
        refine ⟨261920686269234036448820821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349227581692312048598427761 261920686269234036448820821)
        ·
          refine ⟨3069383042217586364634619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 261920686269234036448820821 3069383042217586364634619)
          ·
            refine ⟨4604074563326379546951929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069383042217586364634619 4604074563326379546951929)
            ·
              refine ⟨3453055922494784660213947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4604074563326379546951929 3453055922494784660213947)
              ·
                refine ⟨5179583883742176990320921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453055922494784660213947 5179583883742176990320921)
                ·
                  refine ⟨3884687912806632742740691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179583883742176990320921 3884687912806632742740691)
                  ·
                    refine ⟨5827031869209949114111037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884687912806632742740691 5827031869209949114111037)
                    ·
                      refine ⟨2185136950953730917791639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827031869209949114111037 2185136950953730917791639)
                      ·
                        rfl

theorem cell23_4255539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 1, 3].length) (baseStart_4255539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255539 prefixEnd_4255539 := by exact prefixLift 4255539
  have htrace : WordTrace (prefixWord ++ tailWord_4255539) baseStart_4255539 baseEnd_4255539 := by
    simpa [prefixWord, tailWord_4255539, baseEnd_4255539] using wordTrace_append hprefix tailTrace_4255539
  have hstable : (prefixWord ++ tailWord_4255539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255539).length < 2 ^ (prefixWord ++ tailWord_4255539).sum := by decide
  have hdescent : baseEnd_4255539 < baseStart_4255539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255591 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_4255591 : Nat := 118140960795 + 4255591 * 2 ^ 59
def prefixEnd_4255591 : Nat := 4983230072969 + 3 ^ 40 * 4255591 * 2
def baseEnd_4255591 : Nat := 2185163651947764714341399

theorem tailTrace_4255591 : CollatzResearch.WordTrace tailWord_4255591 prefixEnd_4255591 2185163651947764714341399 := by
  unfold tailWord_4255591
  simp only [CollatzResearch.WordTrace]
  refine ⟨155214155125728078924638627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103476103417152052616425751 155214155125728078924638627)
  ·
    refine ⟨232821232688592118386957941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155214155125728078924638627 232821232688592118386957941)
    ·
      refine ⟨21826990564555511098777307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232821232688592118386957941 21826990564555511098777307)
      ·
        refine ⟨32740485846833266648165961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21826990564555511098777307 32740485846833266648165961)
        ·
          refine ⟨24555364385124949986124471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32740485846833266648165961 24555364385124949986124471)
          ·
            refine ⟨36833046577687424979186707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24555364385124949986124471 36833046577687424979186707)
            ·
              refine ⟨55249569866531137468780061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36833046577687424979186707 55249569866531137468780061)
              ·
                refine ⟨20718588699949176550792523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55249569866531137468780061 20718588699949176550792523)
                ·
                  refine ⟨31077883049923764826188785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20718588699949176550792523 31077883049923764826188785)
                  ·
                    refine ⟨23308412287442823619641589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31077883049923764826188785 23308412287442823619641589)
                    ·
                      refine ⟨2185163651947764714341399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23308412287442823619641589 2185163651947764714341399)
                      ·
                        rfl

theorem cell23_4255591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_4255591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255591 prefixEnd_4255591 := by exact prefixLift 4255591
  have htrace : WordTrace (prefixWord ++ tailWord_4255591) baseStart_4255591 baseEnd_4255591 := by
    simpa [prefixWord, tailWord_4255591, baseEnd_4255591] using wordTrace_append hprefix tailTrace_4255591
  have hstable : (prefixWord ++ tailWord_4255591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255591).length < 2 ^ (prefixWord ++ tailWord_4255591).sum := by decide
  have hdescent : baseEnd_4255591 < baseStart_4255591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255601 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_4255601 : Nat := 118140960795 + 4255601 * 2 ^ 59
def prefixEnd_4255601 : Nat := 4983230072969 + 3 ^ 40 * 4255601 * 2
def baseEnd_4255601 : Nat := 2185168786754309675216353

theorem tailTrace_4255601 : CollatzResearch.WordTrace tailWord_4255601 prefixEnd_4255601 2185168786754309675216353 := by
  unfold tailWord_4255601
  simp only [CollatzResearch.WordTrace]
  refine ⟨155214519855691850632502657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103476346570461233755001771 155214519855691850632502657)
  ·
    refine ⟨116410889891768887974376993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155214519855691850632502657 116410889891768887974376993)
    ·
      refine ⟨87308167418826665980782745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116410889891768887974376993 87308167418826665980782745)
      ·
        refine ⟨65481125564119999485587059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87308167418826665980782745 65481125564119999485587059)
        ·
          refine ⟨98221688346179999228380589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65481125564119999485587059 98221688346179999228380589)
          ·
            refine ⟨36833133129817499710642721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98221688346179999228380589 36833133129817499710642721)
            ·
              refine ⟨27624849847363124782982041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36833133129817499710642721 27624849847363124782982041)
              ·
                refine ⟨20718637385522343587236531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27624849847363124782982041 20718637385522343587236531)
                ·
                  refine ⟨31077956078283515380854797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20718637385522343587236531 31077956078283515380854797)
                  ·
                    refine ⟨11654233529356318267820549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31077956078283515380854797 11654233529356318267820549)
                    ·
                      refine ⟨2185168786754309675216353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11654233529356318267820549 2185168786754309675216353)
                      ·
                        rfl

theorem cell23_4255601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_4255601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255601 prefixEnd_4255601 := by exact prefixLift 4255601
  have htrace : WordTrace (prefixWord ++ tailWord_4255601) baseStart_4255601 baseEnd_4255601 := by
    simpa [prefixWord, tailWord_4255601, baseEnd_4255601] using wordTrace_append hprefix tailTrace_4255601
  have hstable : (prefixWord ++ tailWord_4255601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255601).length < 2 ^ (prefixWord ++ tailWord_4255601).sum := by decide
  have hdescent : baseEnd_4255601 < baseStart_4255601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255645 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4255645 : Nat := 118140960795 + 4255645 * 2 ^ 59
def prefixEnd_4255645 : Nat := 4983230072969 + 3 ^ 40 * 4255645 * 2
def baseEnd_4255645 : Nat := 728397126634369167688717

theorem tailTrace_4255645 : CollatzResearch.WordTrace tailWord_4255645 prefixEnd_4255645 728397126634369167688717 := by
  unfold tailWord_4255645
  simp only [CollatzResearch.WordTrace]
  refine ⟨155216124667532446147104389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103477416445021630764736259 155216124667532446147104389)
  ·
    refine ⟨29103023375162333652582073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155216124667532446147104389 29103023375162333652582073)
    ·
      refine ⟨21827267531371750239436555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29103023375162333652582073 21827267531371750239436555)
      ·
        refine ⟨32740901297057625359154833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21827267531371750239436555 32740901297057625359154833)
        ·
          refine ⟨24555675972793219019366125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32740901297057625359154833 24555675972793219019366125)
          ·
            refine ⟨9208378489797457132262297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24555675972793219019366125 9208378489797457132262297)
            ·
              refine ⟨6906283867348092849196723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9208378489797457132262297 6906283867348092849196723)
              ·
                refine ⟨10359425801022139273795085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6906283867348092849196723 10359425801022139273795085)
                ·
                  refine ⟨3884784675383302227673157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10359425801022139273795085 3884784675383302227673157)
                  ·
                    refine ⟨728397126634369167688717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3884784675383302227673157 728397126634369167688717)
                    ·
                      rfl

theorem cell23_4255645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4255645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255645 prefixEnd_4255645 := by exact prefixLift 4255645
  have htrace : WordTrace (prefixWord ++ tailWord_4255645) baseStart_4255645 baseEnd_4255645 := by
    simpa [prefixWord, tailWord_4255645, baseEnd_4255645] using wordTrace_append hprefix tailTrace_4255645
  have hstable : (prefixWord ++ tailWord_4255645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255645).length < 2 ^ (prefixWord ++ tailWord_4255645).sum := by decide
  have hdescent : baseEnd_4255645 < baseStart_4255645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255695 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 2, 3, 2]
def baseStart_4255695 : Nat := 118140960795 + 4255695 * 2 ^ 59
def prefixEnd_4255695 : Nat := 4983230072969 + 3 ^ 40 * 4255695 * 2
def baseEnd_4255695 : Nat := 2185217053935832307440921

theorem tailTrace_4255695 : CollatzResearch.WordTrace tailWord_4255695 prefixEnd_4255695 2185217053935832307440921 := by
  unfold tailWord_4255695
  simp only [CollatzResearch.WordTrace]
  refine ⟨155217948317351304686424539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103478632211567536457616359 155217948317351304686424539)
  ·
    refine ⟨232826922476026957029636809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155217948317351304686424539 232826922476026957029636809)
    ·
      refine ⟨174620191857020217772227607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232826922476026957029636809 174620191857020217772227607)
      ·
        refine ⟨261930287785530326658341411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174620191857020217772227607 261930287785530326658341411)
        ·
          refine ⟨392895431678295489987512117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261930287785530326658341411 392895431678295489987512117)
          ·
            refine ⟨36833946719840202186329261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 392895431678295489987512117 36833946719840202186329261)
            ·
              refine ⟨13812730019940075819873473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36833946719840202186329261 13812730019940075819873473)
              ·
                refine ⟨10359547514955056864905105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13812730019940075819873473 10359547514955056864905105)
                ·
                  refine ⟨7769660636216292648678829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10359547514955056864905105 7769660636216292648678829)
                  ·
                    refine ⟨2913622738581109743254561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7769660636216292648678829 2913622738581109743254561)
                    ·
                      refine ⟨2185217053935832307440921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913622738581109743254561 2185217053935832307440921)
                      ·
                        rfl

theorem cell23_4255695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3, 2].length) (baseStart_4255695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255695 prefixEnd_4255695 := by exact prefixLift 4255695
  have htrace : WordTrace (prefixWord ++ tailWord_4255695) baseStart_4255695 baseEnd_4255695 := by
    simpa [prefixWord, tailWord_4255695, baseEnd_4255695] using wordTrace_append hprefix tailTrace_4255695
  have hstable : (prefixWord ++ tailWord_4255695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255695).length < 2 ^ (prefixWord ++ tailWord_4255695).sum := by decide
  have hdescent : baseEnd_4255695 < baseStart_4255695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255709 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 6]
def baseStart_4255709 : Nat := 118140960795 + 4255709 * 2 ^ 59
def prefixEnd_4255709 : Nat := 4983230072969 + 3 ^ 40 * 4255709 * 2
def baseEnd_4255709 : Nat := 242802693629443916962873

theorem tailTrace_4255709 : CollatzResearch.WordTrace tailWord_4255709 prefixEnd_4255709 242802693629443916962873 := by
  unfold tailWord_4255709
  simp only [CollatzResearch.WordTrace]
  refine ⟨155218458939300585077434181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103478972626200390051622787 155218458939300585077434181)
  ·
    refine ⟨29103461051118859702018909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155218458939300585077434181 29103461051118859702018909)
    ·
      refine ⟨10913797894169572388257091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29103461051118859702018909 10913797894169572388257091)
      ·
        refine ⟨16370696841254358582385637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10913797894169572388257091 16370696841254358582385637)
        ·
          refine ⟨3069505657735192234197307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16370696841254358582385637 3069505657735192234197307)
          ·
            refine ⟨4604258486602788351295961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069505657735192234197307 4604258486602788351295961)
            ·
              refine ⟨3453193864952091263471971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4604258486602788351295961 3453193864952091263471971)
              ·
                refine ⟨5179790797428136895207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453193864952091263471971 5179790797428136895207957)
                ·
                  refine ⟨242802693629443916962873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5179790797428136895207957 242802693629443916962873)
                  ·
                    rfl

theorem cell23_4255709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_4255709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255709 prefixEnd_4255709 := by exact prefixLift 4255709
  have htrace : WordTrace (prefixWord ++ tailWord_4255709) baseStart_4255709 baseEnd_4255709 := by
    simpa [prefixWord, tailWord_4255709, baseEnd_4255709] using wordTrace_append hprefix tailTrace_4255709
  have hstable : (prefixWord ++ tailWord_4255709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255709).length < 2 ^ (prefixWord ++ tailWord_4255709).sum := by decide
  have hdescent : baseEnd_4255709 < baseStart_4255709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255748 : List Nat := [2, 3, 2, 4, 12]
def baseStart_4255748 : Nat := 118140960795 + 4255748 * 2 ^ 59
def prefixEnd_4255748 : Nat := 4983230072969 + 3 ^ 40 * 4255748 * 2
def baseEnd_4255748 : Nat := 2997591589040494650313

theorem tailTrace_4255748 : CollatzResearch.WordTrace tailWord_4255748 prefixEnd_4255748 2997591589040494650313 := by
  unfold tailWord_4255748
  simp only [CollatzResearch.WordTrace]
  refine ⟨77609940693079647369051949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103479920924106196492069265 77609940693079647369051949)
  ·
    refine ⟨29103727759904867763394481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77609940693079647369051949 29103727759904867763394481)
    ·
      refine ⟨21827795819928650822545861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29103727759904867763394481 21827795819928650822545861)
      ·
        refine ⟨4092711716236622029227349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21827795819928650822545861 4092711716236622029227349)
        ·
          refine ⟨2997591589040494650313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4092711716236622029227349 2997591589040494650313)
          ·
            rfl

theorem cell23_4255748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 12].length) (baseStart_4255748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255748 prefixEnd_4255748 := by exact prefixLift 4255748
  have htrace : WordTrace (prefixWord ++ tailWord_4255748) baseStart_4255748 baseEnd_4255748 := by
    simpa [prefixWord, tailWord_4255748, baseEnd_4255748] using wordTrace_append hprefix tailTrace_4255748
  have hstable : (prefixWord ++ tailWord_4255748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255748).length < 2 ^ (prefixWord ++ tailWord_4255748).sum := by decide
  have hdescent : baseEnd_4255748 < baseStart_4255748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255765 : List Nat := [1, 3, 2, 1, 5, 2, 1, 8]
def baseStart_4255765 : Nat := 118140960795 + 4255765 * 2 ^ 59
def prefixEnd_4255765 : Nat := 4983230072969 + 3 ^ 40 * 4255765 * 2
def baseEnd_4255765 : Nat := 80935296206727667909837

theorem tailTrace_4255765 : CollatzResearch.WordTrace tailWord_4255765 prefixEnd_4255765 80935296206727667909837 := by
  unfold tailWord_4255765
  simp only [CollatzResearch.WordTrace]
  refine ⟨155220501427097706641472749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103480334284731804427648499 155220501427097706641472749)
  ·
    refine ⟨58207688035161639990552281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155220501427097706641472749 58207688035161639990552281)
    ·
      refine ⟨43655766026371229992914211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58207688035161639990552281 43655766026371229992914211)
      ·
        refine ⟨65483649039556844989371317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43655766026371229992914211 65483649039556844989371317)
        ·
          refine ⟨6139092097458454217753561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65483649039556844989371317 6139092097458454217753561)
          ·
            refine ⟨4604319073093840663315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6139092097458454217753561 4604319073093840663315171)
            ·
              refine ⟨6906478609640760994972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604319073093840663315171 6906478609640760994972757)
              ·
                refine ⟨80935296206727667909837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6906478609640760994972757 80935296206727667909837)
                ·
                  rfl

theorem cell23_4255765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 8].length) (baseStart_4255765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255765 prefixEnd_4255765 := by exact prefixLift 4255765
  have htrace : WordTrace (prefixWord ++ tailWord_4255765) baseStart_4255765 baseEnd_4255765 := by
    simpa [prefixWord, tailWord_4255765, baseEnd_4255765] using wordTrace_append hprefix tailTrace_4255765
  have hstable : (prefixWord ++ tailWord_4255765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255765).length < 2 ^ (prefixWord ++ tailWord_4255765).sum := by decide
  have hdescent : baseEnd_4255765 < baseStart_4255765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255775 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_4255775 : Nat := 118140960795 + 4255775 * 2 ^ 59
def prefixEnd_4255775 : Nat := 4983230072969 + 3 ^ 40 * 4255775 * 2
def baseEnd_4255775 : Nat := 2185258132388191994440553

theorem tailTrace_4255775 : CollatzResearch.WordTrace tailWord_4255775 prefixEnd_4255775 2185258132388191994440553 := by
  unfold tailWord_4255775
  simp only [CollatzResearch.WordTrace]
  refine ⟨155220866157061478349336779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103480577438040985566224519 155220866157061478349336779)
  ·
    refine ⟨232831299235592217524005169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155220866157061478349336779 232831299235592217524005169)
    ·
      refine ⟨174623474426694163143003877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232831299235592217524005169 174623474426694163143003877)
      ·
        refine ⟨32741901455005155589313227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174623474426694163143003877 32741901455005155589313227)
        ·
          refine ⟨49112852182507733383969841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32741901455005155589313227 49112852182507733383969841)
          ·
            refine ⟨36834639136880800037977381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49112852182507733383969841 36834639136880800037977381)
            ·
              refine ⟨6906494838165150007120759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36834639136880800037977381 6906494838165150007120759)
              ·
                refine ⟨10359742257247725010681139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6906494838165150007120759 10359742257247725010681139)
                ·
                  refine ⟨15539613385871587516021709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10359742257247725010681139 15539613385871587516021709)
                  ·
                    refine ⟨5827355019701845318508141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15539613385871587516021709 5827355019701845318508141)
                    ·
                      refine ⟨2185258132388191994440553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827355019701845318508141 2185258132388191994440553)
                      ·
                        rfl

theorem cell23_4255775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_4255775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255775 prefixEnd_4255775 := by exact prefixLift 4255775
  have htrace : WordTrace (prefixWord ++ tailWord_4255775) baseStart_4255775 baseEnd_4255775 := by
    simpa [prefixWord, tailWord_4255775, baseEnd_4255775] using wordTrace_append hprefix tailTrace_4255775
  have hstable : (prefixWord ++ tailWord_4255775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255775).length < 2 ^ (prefixWord ++ tailWord_4255775).sum := by decide
  have hdescent : baseEnd_4255775 < baseStart_4255775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255778 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4255778 : Nat := 118140960795 + 4255778 * 2 ^ 59
def prefixEnd_4255778 : Nat := 4983230072969 + 3 ^ 40 * 4255778 * 2
def baseEnd_4255778 : Nat := 728419890943385160901013

theorem tailTrace_4255778 : CollatzResearch.WordTrace tailWord_4255778 prefixEnd_4255778 728419890943385160901013 := by
  unfold tailWord_4255778
  simp only [CollatzResearch.WordTrace]
  refine ⟨38805243894012652465423997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103480650384033739907797325 38805243894012652465423997)
  ·
    refine ⟨14551966460254744674533999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38805243894012652465423997 14551966460254744674533999)
    ·
      refine ⟨21827949690382117011800999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14551966460254744674533999 21827949690382117011800999)
      ·
        refine ⟨32741924535573175517701499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21827949690382117011800999 32741924535573175517701499)
        ·
          refine ⟨49112886803359763276552249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32741924535573175517701499 49112886803359763276552249)
          ·
            refine ⟨36834665102519822457414187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49112886803359763276552249 36834665102519822457414187)
            ·
              refine ⟨55251997653779733686121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36834665102519822457414187 55251997653779733686121281)
              ·
                refine ⟨41438998240334800264590961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55251997653779733686121281 41438998240334800264590961)
                ·
                  refine ⟨31079248680251100198443221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41438998240334800264590961 31079248680251100198443221)
                  ·
                    refine ⟨728419890943385160901013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31079248680251100198443221 728419890943385160901013)
                    ·
                      rfl

theorem cell23_4255778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4255778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255778 prefixEnd_4255778 := by exact prefixLift 4255778
  have htrace : WordTrace (prefixWord ++ tailWord_4255778) baseStart_4255778 baseEnd_4255778 := by
    simpa [prefixWord, tailWord_4255778, baseEnd_4255778] using wordTrace_append hprefix tailTrace_4255778
  have hstable : (prefixWord ++ tailWord_4255778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255778).length < 2 ^ (prefixWord ++ tailWord_4255778).sum := by decide
  have hdescent : baseEnd_4255778 < baseStart_4255778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255808 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_4255808 : Nat := 118140960795 + 4255808 * 2 ^ 59
def prefixEnd_4255808 : Nat := 4983230072969 + 3 ^ 40 * 4255808 * 2
def baseEnd_4255808 : Nat := 728425025749930121775967

theorem tailTrace_4255808 : CollatzResearch.WordTrace tailWord_4255808 prefixEnd_4255808 728425025749930121775967 := by
  unfold tailWord_4255808
  simp only [CollatzResearch.WordTrace]
  refine ⟨77611034882970962492644039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103481379843961283323525385 77611034882970962492644039)
  ·
    refine ⟨116416552324456443738966059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77611034882970962492644039 116416552324456443738966059)
    ·
      refine ⟨174624828486684665608449089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116416552324456443738966059 174624828486684665608449089)
      ·
        refine ⟨130968621365013499206336817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174624828486684665608449089 130968621365013499206336817)
        ·
          refine ⟨98226466023760124404752613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130968621365013499206336817 98226466023760124404752613)
          ·
            refine ⟨18417462379455023325891115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98226466023760124404752613 18417462379455023325891115)
            ·
              refine ⟨27626193569182534988836673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18417462379455023325891115 27626193569182534988836673)
              ·
                refine ⟨20719645176886901241627505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27626193569182534988836673 20719645176886901241627505)
                ·
                  refine ⟨15539733882665175931220629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20719645176886901241627505 15539733882665175931220629)
                  ·
                    refine ⟨728425025749930121775967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15539733882665175931220629 728425025749930121775967)
                    ·
                      rfl

theorem cell23_4255808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_4255808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255808 prefixEnd_4255808 := by exact prefixLift 4255808
  have htrace : WordTrace (prefixWord ++ tailWord_4255808) baseStart_4255808 baseEnd_4255808 := by
    simpa [prefixWord, tailWord_4255808, baseEnd_4255808] using wordTrace_append hprefix tailTrace_4255808
  have hstable : (prefixWord ++ tailWord_4255808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255808).length < 2 ^ (prefixWord ++ tailWord_4255808).sum := by decide
  have hdescent : baseEnd_4255808 < baseStart_4255808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255809 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4255809 : Nat := 118140960795 + 4255809 * 2 ^ 59
def prefixEnd_4255809 : Nat := 4983230072969 + 3 ^ 40 * 4255809 * 2
def baseEnd_4255809 : Nat := 2185275590730444861415397

theorem tailTrace_4255809 : CollatzResearch.WordTrace tailWord_4255809 prefixEnd_4255809 2185275590730444861415397 := by
  unfold tailWord_4255809
  simp only [CollatzResearch.WordTrace]
  refine ⟨155222106238938302156074481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103481404159292201437382987 155222106238938302156074481)
  ·
    refine ⟨116416579679203726617055861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155222106238938302156074481 116416579679203726617055861)
    ·
      refine ⟨10914054344925349370348987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116416579679203726617055861 10914054344925349370348987)
      ·
        refine ⟨16371081517388024055523481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10914054344925349370348987 16371081517388024055523481)
        ·
          refine ⟨12278311138041018041642611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16371081517388024055523481 12278311138041018041642611)
          ·
            refine ⟨18417466707061527062463917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12278311138041018041642611 18417466707061527062463917)
            ·
              refine ⟨6906550015148072648423969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18417466707061527062463917 6906550015148072648423969)
              ·
                refine ⟨5179912511361054486317977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6906550015148072648423969 5179912511361054486317977)
                ·
                  refine ⟨3884934383520790864738483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179912511361054486317977 3884934383520790864738483)
                  ·
                    refine ⟨5827401575281186297107725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884934383520790864738483 5827401575281186297107725)
                    ·
                      refine ⟨2185275590730444861415397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827401575281186297107725 2185275590730444861415397)
                      ·
                        rfl

theorem cell23_4255809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4255809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255809 prefixEnd_4255809 := by exact prefixLift 4255809
  have htrace : WordTrace (prefixWord ++ tailWord_4255809) baseStart_4255809 baseEnd_4255809 := by
    simpa [prefixWord, tailWord_4255809, baseEnd_4255809] using wordTrace_append hprefix tailTrace_4255809
  have hstable : (prefixWord ++ tailWord_4255809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255809).length < 2 ^ (prefixWord ++ tailWord_4255809).sum := by decide
  have hdescent : baseEnd_4255809 < baseStart_4255809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_4255818 : Nat := 118140960795 + 4255818 * 2 ^ 59
def prefixEnd_4255818 : Nat := 4983230072969 + 3 ^ 40 * 4255818 * 2
def baseEnd_4255818 : Nat := 2185280212056335326202855

theorem tailTrace_4255818 : CollatzResearch.WordTrace tailWord_4255818 prefixEnd_4255818 2185280212056335326202855 := by
  unfold tailWord_4255818
  simp only [CollatzResearch.WordTrace]
  refine ⟨38805608623976424173288027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103481622997270464462101405 38805608623976424173288027)
  ·
    refine ⟨58208412935964636259932041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38805608623976424173288027 58208412935964636259932041)
    ·
      refine ⟨43656309701973477194949031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58208412935964636259932041 43656309701973477194949031)
      ·
        refine ⟨65484464552960215792423547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43656309701973477194949031 65484464552960215792423547)
        ·
          refine ⟨98226696829440323688635321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65484464552960215792423547 98226696829440323688635321)
          ·
            refine ⟨73670022622080242766476491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98226696829440323688635321 73670022622080242766476491)
            ·
              refine ⟨110505033933120364149714737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73670022622080242766476491 110505033933120364149714737)
              ·
                refine ⟨82878775449840273112286053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110505033933120364149714737 82878775449840273112286053)
                ·
                  refine ⟨15539770396845051208553635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82878775449840273112286053 15539770396845051208553635)
                  ·
                    refine ⟨23309655595267576812830453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15539770396845051208553635 23309655595267576812830453)
                    ·
                      refine ⟨2185280212056335326202855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23309655595267576812830453 2185280212056335326202855)
                      ·
                        rfl

theorem cell23_4255818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_4255818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255818 prefixEnd_4255818 := by exact prefixLift 4255818
  have htrace : WordTrace (prefixWord ++ tailWord_4255818) baseStart_4255818 baseEnd_4255818 := by
    simpa [prefixWord, tailWord_4255818, baseEnd_4255818] using wordTrace_append hprefix tailTrace_4255818
  have hstable : (prefixWord ++ tailWord_4255818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255818).length < 2 ^ (prefixWord ++ tailWord_4255818).sum := by decide
  have hdescent : baseEnd_4255818 < baseStart_4255818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255826 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_4255826 : Nat := 118140960795 + 4255826 * 2 ^ 59
def prefixEnd_4255826 : Nat := 4983230072969 + 3 ^ 40 * 4255826 * 2
def baseEnd_4255826 : Nat := 2185284319901571294902819

theorem tailTrace_4255826 : CollatzResearch.WordTrace tailWord_4255826 prefixEnd_4255826 2185284319901571294902819 := by
  unfold tailWord_4255826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38805681569969178514860833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103481817519917809372962221 38805681569969178514860833)
  ·
    refine ⟨29104261177476883886145625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38805681569969178514860833 29104261177476883886145625)
    ·
      refine ⟨21828195883107662914609219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29104261177476883886145625 21828195883107662914609219)
      ·
        refine ⟨32742293824661494371913829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21828195883107662914609219 32742293824661494371913829)
        ·
          refine ⟨6139180092124030194733843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32742293824661494371913829 6139180092124030194733843)
          ·
            refine ⟨9208770138186045292100765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139180092124030194733843 9208770138186045292100765)
            ·
              refine ⟨3453288801819766984537787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9208770138186045292100765 3453288801819766984537787)
              ·
                refine ⟨5179933202729650476806681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453288801819766984537787 5179933202729650476806681)
                ·
                  refine ⟨3884949902047237857605011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179933202729650476806681 3884949902047237857605011)
                  ·
                    refine ⟨5827424853070856786407517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884949902047237857605011 5827424853070856786407517)
                    ·
                      refine ⟨2185284319901571294902819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827424853070856786407517 2185284319901571294902819)
                      ·
                        rfl

theorem cell23_4255826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_4255826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255826 prefixEnd_4255826 := by exact prefixLift 4255826
  have htrace : WordTrace (prefixWord ++ tailWord_4255826) baseStart_4255826 baseEnd_4255826 := by
    simpa [prefixWord, tailWord_4255826, baseEnd_4255826] using wordTrace_append hprefix tailTrace_4255826
  have hstable : (prefixWord ++ tailWord_4255826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255826).length < 2 ^ (prefixWord ++ tailWord_4255826).sum := by decide
  have hdescent : baseEnd_4255826 < baseStart_4255826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255832 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_4255832 : Nat := 118140960795 + 4255832 * 2 ^ 59
def prefixEnd_4255832 : Nat := 4983230072969 + 3 ^ 40 * 4255832 * 2
def baseEnd_4255832 : Nat := 2185287400785498271427791

theorem tailTrace_4255832 : CollatzResearch.WordTrace tailWord_4255832 prefixEnd_4255832 2185287400785498271427791 := by
  unfold tailWord_4255832
  simp only [CollatzResearch.WordTrace]
  refine ⟨77611472558927488542080875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103481963411903318056107833 77611472558927488542080875)
  ·
    refine ⟨116417208838391232813121313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77611472558927488542080875 116417208838391232813121313)
    ·
      refine ⟨87312906628793424609840985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116417208838391232813121313 87312906628793424609840985)
      ·
        refine ⟨65484679971595068457380739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87312906628793424609840985 65484679971595068457380739)
        ·
          refine ⟨98227019957392602686071109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65484679971595068457380739 98227019957392602686071109)
          ·
            refine ⟨18417566242011113003638333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98227019957392602686071109 18417566242011113003638333)
            ·
              refine ⟨6906587340754167376364375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18417566242011113003638333 6906587340754167376364375)
              ·
                refine ⟨10359881011131251064546563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6906587340754167376364375 10359881011131251064546563)
                ·
                  refine ⟨15539821516696876596819845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10359881011131251064546563 15539821516696876596819845)
                  ·
                    refine ⟨2913716534380664361903721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15539821516696876596819845 2913716534380664361903721)
                    ·
                      refine ⟨2185287400785498271427791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913716534380664361903721 2185287400785498271427791)
                      ·
                        rfl

theorem cell23_4255832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_4255832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255832 prefixEnd_4255832 := by exact prefixLift 4255832
  have htrace : WordTrace (prefixWord ++ tailWord_4255832) baseStart_4255832 baseEnd_4255832 := by
    simpa [prefixWord, tailWord_4255832, baseEnd_4255832] using wordTrace_append hprefix tailTrace_4255832
  have hstable : (prefixWord ++ tailWord_4255832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255832).length < 2 ^ (prefixWord ++ tailWord_4255832).sum := by decide
  have hdescent : baseEnd_4255832 < baseStart_4255832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255922 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_4255922 : Nat := 118140960795 + 4255922 * 2 ^ 59
def prefixEnd_4255922 : Nat := 4983230072969 + 3 ^ 40 * 4255922 * 2
def baseEnd_4255922 : Nat := 2185333614044402919302377

theorem tailTrace_4255922 : CollatzResearch.WordTrace tailWord_4255922 prefixEnd_4255922 2185333614044402919302377 := by
  unfold tailWord_4255922
  simp only [CollatzResearch.WordTrace]
  refine ⟨38806556921882230613734505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103484151791685948303292013 38806556921882230613734505)
  ·
    refine ⟨29104917691411672960300879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38806556921882230613734505 29104917691411672960300879)
    ·
      refine ⟨43657376537117509440451319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29104917691411672960300879 43657376537117509440451319)
      ·
        refine ⟨65486064805676264160676979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43657376537117509440451319 65486064805676264160676979)
        ·
          refine ⟨98229097208514396241015469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65486064805676264160676979 98229097208514396241015469)
          ·
            refine ⟨36835911453192898590380801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98229097208514396241015469 36835911453192898590380801)
            ·
              refine ⟨27626933589894673942785601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36835911453192898590380801 27626933589894673942785601)
              ·
                refine ⟨20720200192421005457089201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27626933589894673942785601 20720200192421005457089201)
                ·
                  refine ⟨15540150144315754092816901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20720200192421005457089201 15540150144315754092816901)
                  ·
                    refine ⟨2913778152059203892403169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15540150144315754092816901 2913778152059203892403169)
                    ·
                      refine ⟨2185333614044402919302377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913778152059203892403169 2185333614044402919302377)
                      ·
                        rfl

theorem cell23_4255922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_4255922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255922 prefixEnd_4255922 := by exact prefixLift 4255922
  have htrace : WordTrace (prefixWord ++ tailWord_4255922) baseStart_4255922 baseEnd_4255922 := by
    simpa [prefixWord, tailWord_4255922, baseEnd_4255922] using wordTrace_append hprefix tailTrace_4255922
  have hstable : (prefixWord ++ tailWord_4255922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255922).length < 2 ^ (prefixWord ++ tailWord_4255922).sum := by decide
  have hdescent : baseEnd_4255922 < baseStart_4255922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4255972 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_4255972 : Nat := 118140960795 + 4255972 * 2 ^ 59
def prefixEnd_4255972 : Nat := 4983230072969 + 3 ^ 40 * 4255972 * 2
def baseEnd_4255972 : Nat := 2185359288077127723677147

theorem tailTrace_4255972 : CollatzResearch.WordTrace tailWord_4255972 prefixEnd_4255972 2185359288077127723677147 := by
  unfold tailWord_4255972
  simp only [CollatzResearch.WordTrace]
  refine ⟨77614025668673890497129085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103485367558231853996172113 77614025668673890497129085)
  ·
    refine ⟨29105259625752708936423407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77614025668673890497129085 29105259625752708936423407)
    ·
      refine ⟨43657889438629063404635111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29105259625752708936423407 43657889438629063404635111)
      ·
        refine ⟨65486834157943595106952667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43657889438629063404635111 65486834157943595106952667)
        ·
          refine ⟨98230251236915392660429001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65486834157943595106952667 98230251236915392660429001)
          ·
            refine ⟨73672688427686544495321751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98230251236915392660429001 73672688427686544495321751)
            ·
              refine ⟨110509032641529816742982627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73672688427686544495321751 110509032641529816742982627)
              ·
                refine ⟨165763548962294725114473941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110509032641529816742982627 165763548962294725114473941)
                ·
                  refine ⟨3885083178803782619870483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 165763548962294725114473941 3885083178803782619870483)
                  ·
                    refine ⟨5827624768205673929805725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885083178803782619870483 5827624768205673929805725)
                    ·
                      refine ⟨2185359288077127723677147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827624768205673929805725 2185359288077127723677147)
                      ·
                        rfl

theorem cell23_4255972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_4255972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4255972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4255972 prefixEnd_4255972 := by exact prefixLift 4255972
  have htrace : WordTrace (prefixWord ++ tailWord_4255972) baseStart_4255972 baseEnd_4255972 := by
    simpa [prefixWord, tailWord_4255972, baseEnd_4255972] using wordTrace_append hprefix tailTrace_4255972
  have hstable : (prefixWord ++ tailWord_4255972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4255972).length < 2 ^ (prefixWord ++ tailWord_4255972).sum := by decide
  have hdescent : baseEnd_4255972 < baseStart_4255972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4255972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256005 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_4256005 : Nat := 118140960795 + 4256005 * 2 ^ 59
def prefixEnd_4256005 : Nat := 4983230072969 + 3 ^ 40 * 4256005 * 2
def baseEnd_4256005 : Nat := 728458744312908698188165

theorem tailTrace_4256005 : CollatzResearch.WordTrace tailWord_4256005 prefixEnd_4256005 728458744312908698188165 := by
  unfold tailWord_4256005
  simp only [CollatzResearch.WordTrace]
  refine ⟨155229254946228227630209469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103486169964152151753472979 155229254946228227630209469)
  ·
    refine ⟨58210970604835585361328551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155229254946228227630209469 58210970604835585361328551)
    ·
      refine ⟨87316455907253378041992827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58210970604835585361328551 87316455907253378041992827)
      ·
        refine ⟨130974683860880067062989241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87316455907253378041992827 130974683860880067062989241)
        ·
          refine ⟨98231012895660050297241931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130974683860880067062989241 98231012895660050297241931)
          ·
            refine ⟨147346519343490075445862897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98231012895660050297241931 147346519343490075445862897)
            ·
              refine ⟨110509889507617556584397173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147346519343490075445862897 110509889507617556584397173)
              ·
                refine ⟨10360302141339145929787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110509889507617556584397173 10360302141339145929787235)
                ·
                  refine ⟨15540453212008718894680853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10360302141339145929787235 15540453212008718894680853)
                  ·
                    refine ⟨728458744312908698188165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15540453212008718894680853 728458744312908698188165)
                    ·
                      rfl

theorem cell23_4256005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_4256005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256005 prefixEnd_4256005 := by exact prefixLift 4256005
  have htrace : WordTrace (prefixWord ++ tailWord_4256005) baseStart_4256005 baseEnd_4256005 := by
    simpa [prefixWord, tailWord_4256005, baseEnd_4256005] using wordTrace_append hprefix tailTrace_4256005
  have hstable : (prefixWord ++ tailWord_4256005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256005).length < 2 ^ (prefixWord ++ tailWord_4256005).sum := by decide
  have hdescent : baseEnd_4256005 < baseStart_4256005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256012 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_4256012 : Nat := 118140960795 + 4256012 * 2 ^ 59
def prefixEnd_4256012 : Nat := 4983230072969 + 3 ^ 40 * 4256012 * 2
def baseEnd_4256012 : Nat := 2185379827303307567176963

theorem tailTrace_4256012 : CollatzResearch.WordTrace tailWord_4256012 prefixEnd_4256012 2185379827303307567176963 := by
  unfold tailWord_4256012
  simp only [CollatzResearch.WordTrace]
  refine ⟨77614755128601433912857145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103486340171468578550476193 77614755128601433912857145)
  ·
    refine ⟨58211066346451075434642859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77614755128601433912857145 58211066346451075434642859)
    ·
      refine ⟨87316599519676613151964289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58211066346451075434642859 87316599519676613151964289)
      ·
        refine ⟨65487449639757459863973217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87316599519676613151964289 65487449639757459863973217)
        ·
          refine ⟨49115587229818094897979913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65487449639757459863973217 49115587229818094897979913)
          ·
            refine ⟨36836690422363571173484935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49115587229818094897979913 36836690422363571173484935)
            ·
              refine ⟨55255035633545356760227403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36836690422363571173484935 55255035633545356760227403)
              ·
                refine ⟨82882553450318035140341105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55255035633545356760227403 82882553450318035140341105)
                ·
                  refine ⟨62161915087738526355255829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82882553450318035140341105 62161915087738526355255829)
                  ·
                    refine ⟨2913839769737743422902617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62161915087738526355255829 2913839769737743422902617)
                    ·
                      refine ⟨2185379827303307567176963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913839769737743422902617 2185379827303307567176963)
                      ·
                        rfl

theorem cell23_4256012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_4256012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256012 prefixEnd_4256012 := by exact prefixLift 4256012
  have htrace : WordTrace (prefixWord ++ tailWord_4256012) baseStart_4256012 baseEnd_4256012 := by
    simpa [prefixWord, tailWord_4256012, baseEnd_4256012] using wordTrace_append hprefix tailTrace_4256012
  have hstable : (prefixWord ++ tailWord_4256012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256012).length < 2 ^ (prefixWord ++ tailWord_4256012).sum := by decide
  have hdescent : baseEnd_4256012 < baseStart_4256012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256015 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_4256015 : Nat := 118140960795 + 4256015 * 2 ^ 59
def prefixEnd_4256015 : Nat := 4983230072969 + 3 ^ 40 * 4256015 * 2
def baseEnd_4256015 : Nat := 2185381367745271055439449

theorem tailTrace_4256015 : CollatzResearch.WordTrace tailWord_4256015 prefixEnd_4256015 2185381367745271055439449 := by
  unfold tailWord_4256015
  simp only [CollatzResearch.WordTrace]
  refine ⟨155229619676191999338073499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103486413117461332892048999 155229619676191999338073499)
  ·
    refine ⟨232844429514287999007110249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155229619676191999338073499 232844429514287999007110249)
    ·
      refine ⟨174633322135715999255332687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232844429514287999007110249 174633322135715999255332687)
      ·
        refine ⟨261949983203573998882999031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174633322135715999255332687 261949983203573998882999031)
        ·
          refine ⟨392924974805360998324498547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261949983203573998882999031 392924974805360998324498547)
          ·
            refine ⟨589387462208041497486747821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392924974805360998324498547 589387462208041497486747821)
            ·
              refine ⟨221020298328015561557530433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 589387462208041497486747821 221020298328015561557530433)
              ·
                refine ⟨165765223746011671168147825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221020298328015561557530433 165765223746011671168147825)
                ·
                  refine ⟨124323917809508753376110869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165765223746011671168147825 124323917809508753376110869)
                  ·
                    refine ⟨5827683647320722814505197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124323917809508753376110869 5827683647320722814505197)
                    ·
                      refine ⟨2185381367745271055439449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827683647320722814505197 2185381367745271055439449)
                      ·
                        rfl

theorem cell23_4256015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_4256015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256015 prefixEnd_4256015 := by exact prefixLift 4256015
  have htrace : WordTrace (prefixWord ++ tailWord_4256015) baseStart_4256015 baseEnd_4256015 := by
    simpa [prefixWord, tailWord_4256015, baseEnd_4256015] using wordTrace_append hprefix tailTrace_4256015
  have hstable : (prefixWord ++ tailWord_4256015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256015).length < 2 ^ (prefixWord ++ tailWord_4256015).sum := by decide
  have hdescent : baseEnd_4256015 < baseStart_4256015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256023 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4256023 : Nat := 118140960795 + 4256023 * 2 ^ 59
def prefixEnd_4256023 : Nat := 4983230072969 + 3 ^ 40 * 4256023 * 2
def baseEnd_4256023 : Nat := 2185385475590507024139413

theorem tailTrace_4256023 : CollatzResearch.WordTrace tailWord_4256023 prefixEnd_4256023 2185385475590507024139413 := by
  unfold tailWord_4256023
  simp only [CollatzResearch.WordTrace]
  refine ⟨155229911460163016704364723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103486607640108677802909815 155229911460163016704364723)
  ·
    refine ⟨232844867190244525056547085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155229911460163016704364723 232844867190244525056547085)
    ·
      refine ⟨87316825196341696896205157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232844867190244525056547085 87316825196341696896205157)
      ·
        refine ⟨16371904724314068168038467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87316825196341696896205157 16371904724314068168038467)
        ·
          refine ⟨24557857086471102252057701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16371904724314068168038467 24557857086471102252057701)
          ·
            refine ⟨4604598203713331672260819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24557857086471102252057701 4604598203713331672260819)
            ·
              refine ⟨6906897305569997508391229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604598203713331672260819 6906897305569997508391229)
              ·
                refine ⟨2590086489588749065646711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6906897305569997508391229 2590086489588749065646711)
                ·
                  refine ⟨3885129734383123598470067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590086489588749065646711 3885129734383123598470067)
                  ·
                    refine ⟨5827694601574685397705101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885129734383123598470067 5827694601574685397705101)
                    ·
                      refine ⟨2185385475590507024139413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827694601574685397705101 2185385475590507024139413)
                      ·
                        rfl

theorem cell23_4256023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4256023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256023 prefixEnd_4256023 := by exact prefixLift 4256023
  have htrace : WordTrace (prefixWord ++ tailWord_4256023) baseStart_4256023 baseEnd_4256023 := by
    simpa [prefixWord, tailWord_4256023, baseEnd_4256023] using wordTrace_append hprefix tailTrace_4256023
  have hstable : (prefixWord ++ tailWord_4256023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256023).length < 2 ^ (prefixWord ++ tailWord_4256023).sum := by decide
  have hdescent : baseEnd_4256023 < baseStart_4256023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256032 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4256032 : Nat := 118140960795 + 4256032 * 2 ^ 59
def prefixEnd_4256032 : Nat := 4983230072969 + 3 ^ 40 * 4256032 * 2
def baseEnd_4256032 : Nat := 2185390096916397488926871

theorem tailTrace_4256032 : CollatzResearch.WordTrace tailWord_4256032 prefixEnd_4256032 2185390096916397488926871 := by
  unfold tailWord_4256032
  simp only [CollatzResearch.WordTrace]
  refine ⟨77615119858565205620721175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103486826478086940827628233 77615119858565205620721175)
  ·
    refine ⟨116422679787847808431081763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77615119858565205620721175 116422679787847808431081763)
    ·
      refine ⟨174634019681771712646622645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116422679787847808431081763 174634019681771712646622645)
      ·
        refine ⟨16371939345166098060620873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174634019681771712646622645 16371939345166098060620873)
        ·
          refine ⟨12278954508874573545465655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16371939345166098060620873 12278954508874573545465655)
          ·
            refine ⟨18418431763311860318198483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12278954508874573545465655 18418431763311860318198483)
            ·
              refine ⟨27627647644967790477297725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18418431763311860318198483 27627647644967790477297725)
              ·
                refine ⟨10360367866862921428986647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27627647644967790477297725 10360367866862921428986647)
                ·
                  refine ⟨15540551800294382143479971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10360367866862921428986647 15540551800294382143479971)
                  ·
                    refine ⟨23310827700441573215219957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15540551800294382143479971 23310827700441573215219957)
                    ·
                      refine ⟨2185390096916397488926871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23310827700441573215219957 2185390096916397488926871)
                      ·
                        rfl

theorem cell23_4256032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4256032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256032 prefixEnd_4256032 := by exact prefixLift 4256032
  have htrace : WordTrace (prefixWord ++ tailWord_4256032) baseStart_4256032 baseEnd_4256032 := by
    simpa [prefixWord, tailWord_4256032, baseEnd_4256032] using wordTrace_append hprefix tailTrace_4256032
  have hstable : (prefixWord ++ tailWord_4256032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256032).length < 2 ^ (prefixWord ++ tailWord_4256032).sum := by decide
  have hdescent : baseEnd_4256032 < baseStart_4256032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256040 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4256040 : Nat := 118140960795 + 4256040 * 2 ^ 59
def prefixEnd_4256040 : Nat := 4983230072969 + 3 ^ 40 * 4256040 * 2
def baseEnd_4256040 : Nat := 2185394204761633457626835

theorem tailTrace_4256040 : CollatzResearch.WordTrace tailWord_4256040 prefixEnd_4256040 2185394204761633457626835 := by
  unfold tailWord_4256040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77615265750550714303866787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103487021000734285738489049 77615265750550714303866787)
  ·
    refine ⟨116422898625826071455800181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77615265750550714303866787 116422898625826071455800181)
    ·
      refine ⟨10914646746171194198981267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116422898625826071455800181 10914646746171194198981267)
      ·
        refine ⟨16371970119256791298471901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10914646746171194198981267 16371970119256791298471901)
        ·
          refine ⟨6139488794721296736926963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16371970119256791298471901 6139488794721296736926963)
          ·
            refine ⟨9209233192081945105390445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139488794721296736926963 9209233192081945105390445)
            ·
              refine ⟨3453462447030729414521417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9209233192081945105390445 3453462447030729414521417)
              ·
                refine ⟨2590096835273047060891063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453462447030729414521417 2590096835273047060891063)
                ·
                  refine ⟨3885145252909570591336595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590096835273047060891063 3885145252909570591336595)
                  ·
                    refine ⟨5827717879364355887004893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885145252909570591336595 5827717879364355887004893)
                    ·
                      refine ⟨2185394204761633457626835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5827717879364355887004893 2185394204761633457626835)
                      ·
                        rfl

theorem cell23_4256040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4256040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256040 prefixEnd_4256040 := by exact prefixLift 4256040
  have htrace : WordTrace (prefixWord ++ tailWord_4256040) baseStart_4256040 baseEnd_4256040 := by
    simpa [prefixWord, tailWord_4256040, baseEnd_4256040] using wordTrace_append hprefix tailTrace_4256040
  have hstable : (prefixWord ++ tailWord_4256040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256040).length < 2 ^ (prefixWord ++ tailWord_4256040).sum := by decide
  have hdescent : baseEnd_4256040 < baseStart_4256040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256052 : List Nat := [2, 5, 1, 1, 1, 2, 1, 10]
def baseStart_4256052 : Nat := 118140960795 + 4256052 * 2 ^ 59
def prefixEnd_4256052 : Nat := 4983230072969 + 3 ^ 40 * 4256052 * 2
def baseEnd_4256052 : Nat := 80940754315906941136177

theorem tailTrace_4256052 : CollatzResearch.WordTrace tailWord_4256052 prefixEnd_4256052 80940754315906941136177 := by
  unfold tailWord_4256052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77615484588528977328585205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103487312784705303104780273 77615484588528977328585205)
  ·
    refine ⟨7276451680174591624554863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77615484588528977328585205 7276451680174591624554863)
    ·
      refine ⟨10914677520261887436832295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7276451680174591624554863 10914677520261887436832295)
      ·
        refine ⟨16372016280392831155248443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10914677520261887436832295 16372016280392831155248443)
        ·
          refine ⟨24558024420589246732872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372016280392831155248443 24558024420589246732872665)
          ·
            refine ⟨18418518315441935049654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24558024420589246732872665 18418518315441935049654499)
            ·
              refine ⟨27627777473162902574481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18418518315441935049654499 27627777473162902574481749)
              ·
                refine ⟨80940754315906941136177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27627777473162902574481749 80940754315906941136177)
                ·
                  rfl

theorem cell23_4256052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 10].length) (baseStart_4256052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256052 prefixEnd_4256052 := by exact prefixLift 4256052
  have htrace : WordTrace (prefixWord ++ tailWord_4256052) baseStart_4256052 baseEnd_4256052 := by
    simpa [prefixWord, tailWord_4256052, baseEnd_4256052] using wordTrace_append hprefix tailTrace_4256052
  have hstable : (prefixWord ++ tailWord_4256052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256052).length < 2 ^ (prefixWord ++ tailWord_4256052).sum := by decide
  have hdescent : baseEnd_4256052 < baseStart_4256052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256075 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_4256075 : Nat := 118140960795 + 4256075 * 2 ^ 59
def prefixEnd_4256075 : Nat := 4983230072969 + 3 ^ 40 * 4256075 * 2
def baseEnd_4256075 : Nat := 2185412176584540820689173

theorem tailTrace_4256075 : CollatzResearch.WordTrace tailWord_4256075 prefixEnd_4256075 2185412176584540820689173 := by
  unfold tailWord_4256075
  simp only [CollatzResearch.WordTrace]
  refine ⟨155231808055974629585257679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103487872037316419723505119 155231808055974629585257679)
  ·
    refine ⟨232847712083961944377886519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155231808055974629585257679 232847712083961944377886519)
    ·
      refine ⟨349271568125942916566829779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232847712083961944377886519 349271568125942916566829779)
      ·
        refine ⟨523907352188914374850244669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349271568125942916566829779 523907352188914374850244669)
        ·
          refine ⟨196465257070842890568841751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523907352188914374850244669 196465257070842890568841751)
          ·
            refine ⟨294697885606264335853262627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196465257070842890568841751 294697885606264335853262627)
            ·
              refine ⟨442046828409396503779893941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294697885606264335853262627 442046828409396503779893941)
              ·
                refine ⟨41441890163380922229365057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 442046828409396503779893941 41441890163380922229365057)
                ·
                  refine ⟨31081417622535691672023793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41441890163380922229365057 31081417622535691672023793)
                  ·
                    refine ⟨23311063216901768754017845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31081417622535691672023793 23311063216901768754017845)
                    ·
                      refine ⟨2185412176584540820689173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23311063216901768754017845 2185412176584540820689173)
                      ·
                        rfl

theorem cell23_4256075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_4256075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256075 prefixEnd_4256075 := by exact prefixLift 4256075
  have htrace : WordTrace (prefixWord ++ tailWord_4256075) baseStart_4256075 baseEnd_4256075 := by
    simpa [prefixWord, tailWord_4256075, baseEnd_4256075] using wordTrace_append hprefix tailTrace_4256075
  have hstable : (prefixWord ++ tailWord_4256075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256075).length < 2 ^ (prefixWord ++ tailWord_4256075).sum := by decide
  have hdescent : baseEnd_4256075 < baseStart_4256075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256106 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4256106 : Nat := 118140960795 + 4256106 * 2 ^ 59
def prefixEnd_4256106 : Nat := 4983230072969 + 3 ^ 40 * 4256106 * 2
def baseEnd_4256106 : Nat := 2185428094484830199401531

theorem tailTrace_4256106 : CollatzResearch.WordTrace tailWord_4256106 prefixEnd_4256106 2185428094484830199401531 := by
  unfold tailWord_4256106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38808234679715580469909043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103488625812574881253090781 38808234679715580469909043)
  ·
    refine ⟨58212352019573370704863565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38808234679715580469909043 58212352019573370704863565)
    ·
      refine ⟨21829632007340014014323837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58212352019573370704863565 21829632007340014014323837)
      ·
        refine ⟨8186112002752505255371439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21829632007340014014323837 8186112002752505255371439)
        ·
          refine ⟨12279168004128757883057159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186112002752505255371439 12279168004128757883057159)
          ·
            refine ⟨18418752006193136824585739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12279168004128757883057159 18418752006193136824585739)
            ·
              refine ⟨27628128009289705236878609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18418752006193136824585739 27628128009289705236878609)
              ·
                refine ⟨20721096006967278927658957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27628128009289705236878609 20721096006967278927658957)
                ·
                  refine ⟨7770411002612729597872109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20721096006967278927658957 7770411002612729597872109)
                  ·
                    refine ⟨2913904125979773599202041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7770411002612729597872109 2913904125979773599202041)
                    ·
                      refine ⟨2185428094484830199401531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913904125979773599202041 2185428094484830199401531)
                      ·
                        rfl

theorem cell23_4256106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4256106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256106 prefixEnd_4256106 := by exact prefixLift 4256106
  have htrace : WordTrace (prefixWord ++ tailWord_4256106) baseStart_4256106 baseEnd_4256106 := by
    simpa [prefixWord, tailWord_4256106, baseEnd_4256106] using wordTrace_append hprefix tailTrace_4256106
  have hstable : (prefixWord ++ tailWord_4256106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256106).length < 2 ^ (prefixWord ++ tailWord_4256106).sum := by decide
  have hdescent : baseEnd_4256106 < baseStart_4256106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256112 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_4256112 : Nat := 118140960795 + 4256112 * 2 ^ 59
def prefixEnd_4256112 : Nat := 4983230072969 + 3 ^ 40 * 4256112 * 2
def baseEnd_4256112 : Nat := 728477058456252391975501

theorem tailTrace_4256112 : CollatzResearch.WordTrace tailWord_4256112 prefixEnd_4256112 728477058456252391975501 := by
  unfold tailWord_4256112
  simp only [CollatzResearch.WordTrace]
  refine ⟨77616578778420292452177295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103488771704560389936236393 77616578778420292452177295)
  ·
    refine ⟨116424868167630438678265943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77616578778420292452177295 116424868167630438678265943)
    ·
      refine ⟨174637302251445658017398915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116424868167630438678265943 174637302251445658017398915)
      ·
        refine ⟨261955953377168487026098373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174637302251445658017398915 261955953377168487026098373)
        ·
          refine ⟨49116741258219091317393445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261955953377168487026098373 49116741258219091317393445)
          ·
            refine ⟨9209388985916079622011271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49116741258219091317393445 9209388985916079622011271)
            ·
              refine ⟨13814083478874119433016907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9209388985916079622011271 13814083478874119433016907)
              ·
                refine ⟨20721125218311179149525361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13814083478874119433016907 20721125218311179149525361)
                ·
                  refine ⟨15540843913733384362144021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20721125218311179149525361 15540843913733384362144021)
                  ·
                    refine ⟨728477058456252391975501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15540843913733384362144021 728477058456252391975501)
                    ·
                      rfl

theorem cell23_4256112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_4256112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256112 prefixEnd_4256112 := by exact prefixLift 4256112
  have htrace : WordTrace (prefixWord ++ tailWord_4256112) baseStart_4256112 baseEnd_4256112 := by
    simpa [prefixWord, tailWord_4256112, baseEnd_4256112] using wordTrace_append hprefix tailTrace_4256112
  have hstable : (prefixWord ++ tailWord_4256112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256112).length < 2 ^ (prefixWord ++ tailWord_4256112).sum := by decide
  have hdescent : baseEnd_4256112 < baseStart_4256112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256115 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_4256115 : Nat := 118140960795 + 4256115 * 2 ^ 59
def prefixEnd_4256115 : Nat := 4983230072969 + 3 ^ 40 * 4256115 * 2
def baseEnd_4256115 : Nat := 2185432715810720664188989

theorem tailTrace_4256115 : CollatzResearch.WordTrace tailWord_4256115 prefixEnd_4256115 2185432715810720664188989 := by
  unfold tailWord_4256115
  simp only [CollatzResearch.WordTrace]
  refine ⟨155233266975829716416713799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103488844650553144277809199 155233266975829716416713799)
  ·
    refine ⟨232849900463744574625070699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155233266975829716416713799 232849900463744574625070699)
    ·
      refine ⟨349274850695616861937606049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232849900463744574625070699 349274850695616861937606049)
      ·
        refine ⟨261956138021712646453204537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349274850695616861937606049 261956138021712646453204537)
        ·
          refine ⟨196467103516284484839903403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261956138021712646453204537 196467103516284484839903403)
          ·
            refine ⟨294700655274426727259855105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196467103516284484839903403 294700655274426727259855105)
            ·
              refine ⟨221025491455820045444891329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294700655274426727259855105 221025491455820045444891329)
              ·
                refine ⟨165769118591865034083668497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221025491455820045444891329 165769118591865034083668497)
                ·
                  refine ⟨124326838943898775562751373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165769118591865034083668497 124326838943898775562751373)
                  ·
                    refine ⟨46622564603962040836031765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124326838943898775562751373 46622564603962040836031765)
                    ·
                      refine ⟨2185432715810720664188989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46622564603962040836031765 2185432715810720664188989)
                      ·
                        rfl

theorem cell23_4256115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_4256115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256115 prefixEnd_4256115 := by exact prefixLift 4256115
  have htrace : WordTrace (prefixWord ++ tailWord_4256115) baseStart_4256115 baseEnd_4256115 := by
    simpa [prefixWord, tailWord_4256115, baseEnd_4256115] using wordTrace_append hprefix tailTrace_4256115
  have hstable : (prefixWord ++ tailWord_4256115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256115).length < 2 ^ (prefixWord ++ tailWord_4256115).sum := by decide
  have hdescent : baseEnd_4256115 < baseStart_4256115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256132 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4256132 : Nat := 118140960795 + 4256132 * 2 ^ 59
def prefixEnd_4256132 : Nat := 4983230072969 + 3 ^ 40 * 4256132 * 2
def baseEnd_4256132 : Nat := 2185441444981847097676411

theorem tailTrace_4256132 : CollatzResearch.WordTrace tailWord_4256132 prefixEnd_4256132 2185441444981847097676411 := by
  unfold tailWord_4256132
  simp only [CollatzResearch.WordTrace]
  refine ⟨77616943508384064160041325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103489258011178752213388433 77616943508384064160041325)
  ·
    refine ⟨29106353815644024060015497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77616943508384064160041325 29106353815644024060015497)
    ·
      refine ⟨21829765361733018045011623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29106353815644024060015497 21829765361733018045011623)
      ·
        refine ⟨32744648042599527067517435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21829765361733018045011623 32744648042599527067517435)
        ·
          refine ⟨49116972063899290601276153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32744648042599527067517435 49116972063899290601276153)
          ·
            refine ⟨36837729047924467950957115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49116972063899290601276153 36837729047924467950957115)
            ·
              refine ⟨55256593571886701926435673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36837729047924467950957115 55256593571886701926435673)
              ·
                refine ⟨41442445178915026444826755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55256593571886701926435673 41442445178915026444826755)
                ·
                  refine ⟨62163667768372539667240133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41442445178915026444826755 62163667768372539667240133)
                  ·
                    refine ⟨11655687706569851187607525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62163667768372539667240133 11655687706569851187607525)
                    ·
                      refine ⟨2185441444981847097676411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11655687706569851187607525 2185441444981847097676411)
                      ·
                        rfl

theorem cell23_4256132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4256132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256132 prefixEnd_4256132 := by exact prefixLift 4256132
  have htrace : WordTrace (prefixWord ++ tailWord_4256132) baseStart_4256132 baseEnd_4256132 := by
    simpa [prefixWord, tailWord_4256132, baseEnd_4256132] using wordTrace_append hprefix tailTrace_4256132
  have hstable : (prefixWord ++ tailWord_4256132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256132).length < 2 ^ (prefixWord ++ tailWord_4256132).sum := by decide
  have hdescent : baseEnd_4256132 < baseStart_4256132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256136 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_4256136 : Nat := 118140960795 + 4256136 * 2 ^ 59
def prefixEnd_4256136 : Nat := 4983230072969 + 3 ^ 40 * 4256136 * 2
def baseEnd_4256136 : Nat := 2185443498904465082026393

theorem tailTrace_4256136 : CollatzResearch.WordTrace tailWord_4256136 prefixEnd_4256136 2185443498904465082026393 := by
  unfold tailWord_4256136
  simp only [CollatzResearch.WordTrace]
  refine ⟨77617016454376818501614131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103489355272502424668818841 77617016454376818501614131)
  ·
    refine ⟨116425524681565227752421197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77617016454376818501614131 116425524681565227752421197)
    ·
      refine ⟨43659571755586960407157949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116425524681565227752421197 43659571755586960407157949)
      ·
        refine ⟨16372339408345110152684231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43659571755586960407157949 16372339408345110152684231)
        ·
          refine ⟨24558509112517665229026347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372339408345110152684231 24558509112517665229026347)
          ·
            refine ⟨36837763668776497843539521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24558509112517665229026347 36837763668776497843539521)
            ·
              refine ⟨27628322751582373382654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36837763668776497843539521 27628322751582373382654641)
              ·
                refine ⟨20721242063686780036990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27628322751582373382654641 20721242063686780036990981)
                ·
                  refine ⟨3885232886941271256935809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20721242063686780036990981 3885232886941271256935809)
                  ·
                    refine ⟨2913924665205953442701857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3885232886941271256935809 2913924665205953442701857)
                    ·
                      refine ⟨2185443498904465082026393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913924665205953442701857 2185443498904465082026393)
                      ·
                        rfl

theorem cell23_4256136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_4256136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256136 prefixEnd_4256136 := by exact prefixLift 4256136
  have htrace : WordTrace (prefixWord ++ tailWord_4256136) baseStart_4256136 baseEnd_4256136 := by
    simpa [prefixWord, tailWord_4256136, baseEnd_4256136] using wordTrace_append hprefix tailTrace_4256136
  have hstable : (prefixWord ++ tailWord_4256136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256136).length < 2 ^ (prefixWord ++ tailWord_4256136).sum := by decide
  have hdescent : baseEnd_4256136 < baseStart_4256136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256159 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 5]
def baseStart_4256159 : Nat := 118140960795 + 4256159 * 2 ^ 59
def prefixEnd_4256159 : Nat := 4983230072969 + 3 ^ 40 * 4256159 * 2
def baseEnd_4256159 : Nat := 242828367662168721337643

theorem tailTrace_4256159 : CollatzResearch.WordTrace tailWord_4256159 prefixEnd_4256159 242828367662168721337643 := by
  unfold tailWord_4256159
  simp only [CollatzResearch.WordTrace]
  refine ⟨155234871787670311931315531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103489914525113541287543687 155234871787670311931315531)
  ·
    refine ⟨232852307681505467896973297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155234871787670311931315531 232852307681505467896973297)
    ·
      refine ⟨174639230761129100922729973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232852307681505467896973297 174639230761129100922729973)
      ·
        refine ⟨16372427883855853211505935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174639230761129100922729973 16372427883855853211505935)
        ·
          refine ⟨24558641825783779817258903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372427883855853211505935 24558641825783779817258903)
          ·
            refine ⟨36837962738675669725888355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24558641825783779817258903 36837962738675669725888355)
            ·
              refine ⟨55256944108013504588832533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36837962738675669725888355 55256944108013504588832533)
              ·
                refine ⟨2590169255063133027601525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55256944108013504588832533 2590169255063133027601525)
                ·
                  refine ⟨242828367662168721337643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590169255063133027601525 242828367662168721337643)
                  ·
                    rfl

theorem cell23_4256159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 5].length) (baseStart_4256159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256159 prefixEnd_4256159 := by exact prefixLift 4256159
  have htrace : WordTrace (prefixWord ++ tailWord_4256159) baseStart_4256159 baseEnd_4256159 := by
    simpa [prefixWord, tailWord_4256159, baseEnd_4256159] using wordTrace_append hprefix tailTrace_4256159
  have hstable : (prefixWord ++ tailWord_4256159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256159).length < 2 ^ (prefixWord ++ tailWord_4256159).sum := by decide
  have hdescent : baseEnd_4256159 < baseStart_4256159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_4256209 : Nat := 118140960795 + 4256209 * 2 ^ 59
def prefixEnd_4256209 : Nat := 4983230072969 + 3 ^ 40 * 4256209 * 2
def baseEnd_4256209 : Nat := 2185480982992243296413557

theorem tailTrace_4256209 : CollatzResearch.WordTrace tailWord_4256209 prefixEnd_4256209 2185480982992243296413557 := by
  unfold tailWord_4256209
  simp only [CollatzResearch.WordTrace]
  refine ⟨155236695437489170470635681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103491130291659446980423787 155236695437489170470635681)
  ·
    refine ⟨116427521578116877852976761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155236695437489170470635681 116427521578116877852976761)
    ·
      refine ⟨87320641183587658389732571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116427521578116877852976761 87320641183587658389732571)
      ·
        refine ⟨130980961775381487584598857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87320641183587658389732571 130980961775381487584598857)
        ·
          refine ⟨98235721331536115688449143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130980961775381487584598857 98235721331536115688449143)
          ·
            refine ⟨147353581997304173532673715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98235721331536115688449143 147353581997304173532673715)
            ·
              refine ⟨221030372995956260299010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147353581997304173532673715 221030372995956260299010573)
              ·
                refine ⟨82886389873483597612128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221030372995956260299010573 82886389873483597612128965)
                ·
                  refine ⟨15541198101278174552274181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82886389873483597612128965 15541198101278174552274181)
                  ·
                    refine ⟨2913974643989657728551409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15541198101278174552274181 2913974643989657728551409)
                    ·
                      refine ⟨2185480982992243296413557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2913974643989657728551409 2185480982992243296413557)
                      ·
                        rfl

theorem cell23_4256209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_4256209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256209 prefixEnd_4256209 := by exact prefixLift 4256209
  have htrace : WordTrace (prefixWord ++ tailWord_4256209) baseStart_4256209 baseEnd_4256209 := by
    simpa [prefixWord, tailWord_4256209, baseEnd_4256209] using wordTrace_append hprefix tailTrace_4256209
  have hstable : (prefixWord ++ tailWord_4256209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256209).length < 2 ^ (prefixWord ++ tailWord_4256209).sum := by decide
  have hdescent : baseEnd_4256209 < baseStart_4256209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256210 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_4256210 : Nat := 118140960795 + 4256210 * 2 ^ 59
def prefixEnd_4256210 : Nat := 4983230072969 + 3 ^ 40 * 4256210 * 2
def baseEnd_4256210 : Nat := 242831277385877532500117

theorem tailTrace_4256210 : CollatzResearch.WordTrace tailWord_4256210 prefixEnd_4256210 242831277385877532500117 := by
  unfold tailWord_4256210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38809182977621386910355521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103491154606990365094281389 38809182977621386910355521)
  ·
    refine ⟨29106887233216040182766641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38809182977621386910355521 29106887233216040182766641)
    ·
      refine ⟨21830165424912030137074981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29106887233216040182766641 21830165424912030137074981)
      ·
        refine ⟨4093156017171005650701559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21830165424912030137074981 4093156017171005650701559)
        ·
          refine ⟨6139734025756508476052339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093156017171005650701559 6139734025756508476052339)
          ·
            refine ⟨9209601038634762714078509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139734025756508476052339 9209601038634762714078509)
            ·
              refine ⟨3453600389488036017779441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9209601038634762714078509 3453600389488036017779441)
              ·
                refine ⟨2590200292116027013334581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453600389488036017779441 2590200292116027013334581)
                ·
                  refine ⟨242831277385877532500117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590200292116027013334581 242831277385877532500117)
                  ·
                    rfl

theorem cell23_4256210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_4256210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256210 prefixEnd_4256210 := by exact prefixLift 4256210
  have htrace : WordTrace (prefixWord ++ tailWord_4256210) baseStart_4256210 baseEnd_4256210 := by
    simpa [prefixWord, tailWord_4256210, baseEnd_4256210] using wordTrace_append hprefix tailTrace_4256210
  have hstable : (prefixWord ++ tailWord_4256210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256210).length < 2 ^ (prefixWord ++ tailWord_4256210).sum := by decide
  have hdescent : baseEnd_4256210 < baseStart_4256210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256252 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4256252 : Nat := 118140960795 + 4256252 * 2 ^ 59
def prefixEnd_4256252 : Nat := 4983230072969 + 3 ^ 40 * 4256252 * 2
def baseEnd_4256252 : Nat := 2185503062660386628175859

theorem tailTrace_4256252 : CollatzResearch.WordTrace tailWord_4256252 prefixEnd_4256252 2185503062660386628175859 := by
  unfold tailWord_4256252
  simp only [CollatzResearch.WordTrace]
  refine ⟨77619131888166694407225505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103492175850888925876300673 77619131888166694407225505)
  ·
    refine ⟨58214348916125020805419129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77619131888166694407225505 58214348916125020805419129)
    ·
      refine ⟨43660761687093765604064347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58214348916125020805419129 43660761687093765604064347)
      ·
        refine ⟨65491142530640648406096521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43660761687093765604064347 65491142530640648406096521)
        ·
          refine ⟨49118356897980486304572391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65491142530640648406096521 49118356897980486304572391)
          ·
            refine ⟨73677535346970729456858587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49118356897980486304572391 73677535346970729456858587)
            ·
              refine ⟨110516303020456094185287881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73677535346970729456858587 110516303020456094185287881)
              ·
                refine ⟨82887227265342070638965911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110516303020456094185287881 82887227265342070638965911)
                ·
                  refine ⟨124330840898013105958448867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82887227265342070638965911 124330840898013105958448867)
                  ·
                    refine ⟨186496261347019658937673301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124330840898013105958448867 186496261347019658937673301)
                    ·
                      refine ⟨2185503062660386628175859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 186496261347019658937673301 2185503062660386628175859)
                      ·
                        rfl

theorem cell23_4256252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4256252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256252 prefixEnd_4256252 := by exact prefixLift 4256252
  have htrace : WordTrace (prefixWord ++ tailWord_4256252) baseStart_4256252 baseEnd_4256252 := by
    simpa [prefixWord, tailWord_4256252, baseEnd_4256252] using wordTrace_append hprefix tailTrace_4256252
  have hstable : (prefixWord ++ tailWord_4256252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256252).length < 2 ^ (prefixWord ++ tailWord_4256252).sum := by decide
  have hdescent : baseEnd_4256252 < baseStart_4256252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256270 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_4256270 : Nat := 118140960795 + 4256270 * 2 ^ 59
def prefixEnd_4256270 : Nat := 4983230072969 + 3 ^ 40 * 4256270 * 2
def baseEnd_4256270 : Nat := 728504101770722519250259

theorem tailTrace_4256270 : CollatzResearch.WordTrace tailWord_4256270 prefixEnd_4256270 728504101770722519250259 := by
  unfold tailWord_4256270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404865036283522236075783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103492613526845451925737509 19404865036283522236075783)
  ·
    refine ⟨29107297554425283354113675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404865036283522236075783 29107297554425283354113675)
    ·
      refine ⟨43660946331637925031170513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29107297554425283354113675 43660946331637925031170513)
      ·
        refine ⟨32745709748728443773377885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43660946331637925031170513 32745709748728443773377885)
        ·
          refine ⟨12279641155773166415016707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32745709748728443773377885 12279641155773166415016707)
          ·
            refine ⟨18419461733659749622525061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12279641155773166415016707 18419461733659749622525061)
            ·
              refine ⟨3453649075061203054223449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18419461733659749622525061 3453649075061203054223449)
              ·
                refine ⟨2590236806295902290667587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453649075061203054223449 2590236806295902290667587)
                ·
                  refine ⟨3885355209443853436001381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590236806295902290667587 3885355209443853436001381)
                  ·
                    refine ⟨728504101770722519250259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885355209443853436001381 728504101770722519250259)
                    ·
                      rfl

theorem cell23_4256270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_4256270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256270 prefixEnd_4256270 := by exact prefixLift 4256270
  have htrace : WordTrace (prefixWord ++ tailWord_4256270) baseStart_4256270 baseEnd_4256270 := by
    simpa [prefixWord, tailWord_4256270, baseEnd_4256270] using wordTrace_append hprefix tailTrace_4256270
  have hstable : (prefixWord ++ tailWord_4256270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256270).length < 2 ^ (prefixWord ++ tailWord_4256270).sum := by decide
  have hdescent : baseEnd_4256270 < baseStart_4256270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256296 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4256296 : Nat := 118140960795 + 4256296 * 2 ^ 59
def prefixEnd_4256296 : Nat := 4983230072969 + 3 ^ 40 * 4256296 * 2
def baseEnd_4256296 : Nat := 728508551936394818675219

theorem tailTrace_4256296 : CollatzResearch.WordTrace tailWord_4256296 prefixEnd_4256296 728508551936394818675219 := by
  unfold tailWord_4256296
  simp only [CollatzResearch.WordTrace]
  refine ⟨77619934294086992164526371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103493245725449322886035161 77619934294086992164526371)
  ·
    refine ⟨116429901441130488246789557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77619934294086992164526371 116429901441130488246789557)
    ·
      refine ⟨10915303260105983273136521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116429901441130488246789557 10915303260105983273136521)
      ·
        refine ⟨8186477445079487454852391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10915303260105983273136521 8186477445079487454852391)
        ·
          refine ⟨12279716167619231182278587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186477445079487454852391 12279716167619231182278587)
          ·
            refine ⟨18419574251428846773417881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12279716167619231182278587 18419574251428846773417881)
            ·
              refine ⟨13814680688571635080063411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18419574251428846773417881 13814680688571635080063411)
              ·
                refine ⟨20722021032857452620095117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13814680688571635080063411 20722021032857452620095117)
                ·
                  refine ⟨7770757887321544732535669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20722021032857452620095117 7770757887321544732535669)
                  ·
                    refine ⟨728508551936394818675219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7770757887321544732535669 728508551936394818675219)
                    ·
                      rfl

theorem cell23_4256296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4256296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256296 prefixEnd_4256296 := by exact prefixLift 4256296
  have htrace : WordTrace (prefixWord ++ tailWord_4256296) baseStart_4256296 baseEnd_4256296 := by
    simpa [prefixWord, tailWord_4256296, baseEnd_4256296] using wordTrace_append hprefix tailTrace_4256296
  have hstable : (prefixWord ++ tailWord_4256296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256296).length < 2 ^ (prefixWord ++ tailWord_4256296).sum := by decide
  have hdescent : baseEnd_4256296 < baseStart_4256296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256309 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4256309 : Nat := 118140960795 + 4256309 * 2 ^ 59
def prefixEnd_4256309 : Nat := 4983230072969 + 3 ^ 40 * 4256309 * 2
def baseEnd_4256309 : Nat := 728510777019230968387699

theorem tailTrace_4256309 : CollatzResearch.WordTrace tailWord_4256309 prefixEnd_4256309 728510777019230968387699 := by
  unfold tailWord_4256309
  simp only [CollatzResearch.WordTrace]
  refine ⟨155240342737126887549275981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103493561824751258366183987 155240342737126887549275981)
  ·
    refine ⟨58215128526422582830978493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155240342737126887549275981 58215128526422582830978493)
    ·
      refine ⟨21830673197408468561616935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58215128526422582830978493 21830673197408468561616935)
      ·
        refine ⟨32746009796112702842425403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21830673197408468561616935 32746009796112702842425403)
        ·
          refine ⟨49119014694169054263638105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32746009796112702842425403 49119014694169054263638105)
          ·
            refine ⟨36839261020626790697728579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49119014694169054263638105 36839261020626790697728579)
            ·
              refine ⟨55258891530940186046592869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36839261020626790697728579 55258891530940186046592869)
              ·
                refine ⟨10361042162051284883736163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55258891530940186046592869 10361042162051284883736163)
                ·
                  refine ⟨15541563243076927325604245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361042162051284883736163 15541563243076927325604245)
                  ·
                    refine ⟨728510777019230968387699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15541563243076927325604245 728510777019230968387699)
                    ·
                      rfl

theorem cell23_4256309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4256309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256309 prefixEnd_4256309 := by exact prefixLift 4256309
  have htrace : WordTrace (prefixWord ++ tailWord_4256309) baseStart_4256309 baseEnd_4256309 := by
    simpa [prefixWord, tailWord_4256309, baseEnd_4256309] using wordTrace_append hprefix tailTrace_4256309
  have hstable : (prefixWord ++ tailWord_4256309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256309).length < 2 ^ (prefixWord ++ tailWord_4256309).sum := by decide
  have hdescent : baseEnd_4256309 < baseStart_4256309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256319 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_4256319 : Nat := 118140960795 + 4256319 * 2 ^ 59
def prefixEnd_4256319 : Nat := 4983230072969 + 3 ^ 40 * 4256319 * 2
def baseEnd_4256319 : Nat := 2185537465864237866038051

theorem tailTrace_4256319 : CollatzResearch.WordTrace tailWord_4256319 prefixEnd_4256319 2185537465864237866038051 := by
  unfold tailWord_4256319
  simp only [CollatzResearch.WordTrace]
  refine ⟨155240707467090659257140011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103493804978060439504760007 155240707467090659257140011)
  ·
    refine ⟨232861061200635988885710017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155240707467090659257140011 232861061200635988885710017)
    ·
      refine ⟨174645795900476991664282513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232861061200635988885710017 174645795900476991664282513)
      ·
        refine ⟨130984346925357743748211885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174645795900476991664282513 130984346925357743748211885)
        ·
          refine ⟨49119130097009153905579457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130984346925357743748211885 49119130097009153905579457)
          ·
            refine ⟨36839347572756865429184593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49119130097009153905579457 36839347572756865429184593)
            ·
              refine ⟨27629510679567649071888445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36839347572756865429184593 27629510679567649071888445)
              ·
                refine ⟨10361066504837868401958167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27629510679567649071888445 10361066504837868401958167)
                ·
                  refine ⟨15541599757256802602937251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361066504837868401958167 15541599757256802602937251)
                  ·
                    refine ⟨23312399635885203904405877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15541599757256802602937251 23312399635885203904405877)
                    ·
                      refine ⟨2185537465864237866038051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23312399635885203904405877 2185537465864237866038051)
                      ·
                        rfl

theorem cell23_4256319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_4256319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256319 prefixEnd_4256319 := by exact prefixLift 4256319
  have htrace : WordTrace (prefixWord ++ tailWord_4256319) baseStart_4256319 baseEnd_4256319 := by
    simpa [prefixWord, tailWord_4256319, baseEnd_4256319] using wordTrace_append hprefix tailTrace_4256319
  have hstable : (prefixWord ++ tailWord_4256319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256319).length < 2 ^ (prefixWord ++ tailWord_4256319).sum := by decide
  have hdescent : baseEnd_4256319 < baseStart_4256319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256343 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 2, 4]
def baseStart_4256343 : Nat := 118140960795 + 4256343 * 2 ^ 59
def prefixEnd_4256343 : Nat := 4983230072969 + 3 ^ 40 * 4256343 * 2
def baseEnd_4256343 : Nat := 728516596466648590712647

theorem tailTrace_4256343 : CollatzResearch.WordTrace tailWord_4256343 prefixEnd_4256343 728516596466648590712647 := by
  unfold tailWord_4256343
  simp only [CollatzResearch.WordTrace]
  refine ⟨155241582819003711356013683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103494388546002474237342455 155241582819003711356013683)
  ·
    refine ⟨232862374228505567034020525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155241582819003711356013683 232862374228505567034020525)
    ·
      refine ⟨87323390335689587637757697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232862374228505567034020525 87323390335689587637757697)
      ·
        refine ⟨65492542751767190728318273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87323390335689587637757697 65492542751767190728318273)
        ·
          refine ⟨49119407063825393046238705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65492542751767190728318273 49119407063825393046238705)
          ·
            refine ⟨36839555297869044784679029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49119407063825393046238705 36839555297869044784679029)
            ·
              refine ⟨3453708309175222948563659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36839555297869044784679029 3453708309175222948563659)
              ·
                refine ⟨5180562463762834422845489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453708309175222948563659 5180562463762834422845489)
                ·
                  refine ⟨3885421847822125817134117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5180562463762834422845489 3885421847822125817134117)
                  ·
                    refine ⟨728516596466648590712647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885421847822125817134117 728516596466648590712647)
                    ·
                      rfl

theorem cell23_4256343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_4256343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256343 prefixEnd_4256343 := by exact prefixLift 4256343
  have htrace : WordTrace (prefixWord ++ tailWord_4256343) baseStart_4256343 baseEnd_4256343 := by
    simpa [prefixWord, tailWord_4256343, baseEnd_4256343] using wordTrace_append hprefix tailTrace_4256343
  have hstable : (prefixWord ++ tailWord_4256343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256343).length < 2 ^ (prefixWord ++ tailWord_4256343).sum := by decide
  have hdescent : baseEnd_4256343 < baseStart_4256343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256353 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_4256353 : Nat := 118140960795 + 4256353 * 2 ^ 59
def prefixEnd_4256353 : Nat := 4983230072969 + 3 ^ 40 * 4256353 * 2
def baseEnd_4256353 : Nat := 2185554924206490733012895

theorem tailTrace_4256353 : CollatzResearch.WordTrace tailWord_4256353 prefixEnd_4256353 2185554924206490733012895 := by
  unfold tailWord_4256353
  simp only [CollatzResearch.WordTrace]
  refine ⟨155241947548967483063877713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103494631699311655375918475 155241947548967483063877713)
  ·
    refine ⟨116431460661725612297908285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155241947548967483063877713 116431460661725612297908285)
    ·
      refine ⟨43661797748147104611715607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116431460661725612297908285 43661797748147104611715607)
      ·
        refine ⟨65492696622220656917573411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43661797748147104611715607 65492696622220656917573411)
        ·
          refine ⟨98239044933330985376360117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65492696622220656917573411 98239044933330985376360117)
          ·
            refine ⟨9209910462499779879033761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98239044933330985376360117 9209910462499779879033761)
            ·
              refine ⟨6907432846874834909275321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9209910462499779879033761 6907432846874834909275321)
              ·
                refine ⟨5180574635156126181956491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6907432846874834909275321 5180574635156126181956491)
                ·
                  refine ⟨7770861952734189272934737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5180574635156126181956491 7770861952734189272934737)
                  ·
                    refine ⟨5828146464550641954701053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7770861952734189272934737 5828146464550641954701053)
                    ·
                      refine ⟨2185554924206490733012895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828146464550641954701053 2185554924206490733012895)
                      ·
                        rfl

theorem cell23_4256353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_4256353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256353 prefixEnd_4256353 := by exact prefixLift 4256353
  have htrace : WordTrace (prefixWord ++ tailWord_4256353) baseStart_4256353 baseEnd_4256353 := by
    simpa [prefixWord, tailWord_4256353, baseEnd_4256353] using wordTrace_append hprefix tailTrace_4256353
  have hstable : (prefixWord ++ tailWord_4256353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256353).length < 2 ^ (prefixWord ++ tailWord_4256353).sum := by decide
  have hdescent : baseEnd_4256353 < baseStart_4256353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256373 : List Nat := [1, 3, 4, 2, 3, 1, 9]
def baseStart_4256373 : Nat := 118140960795 + 4256373 * 2 ^ 59
def prefixEnd_4256373 : Nat := 4983230072969 + 3 ^ 40 * 4256373 * 2
def baseEnd_4256373 : Nat := 26982286343451613021763

theorem tailTrace_4256373 : CollatzResearch.WordTrace tailWord_4256373 prefixEnd_4256373 26982286343451613021763 := by
  unfold tailWord_4256373
  simp only [CollatzResearch.WordTrace]
  refine ⟨155242677008895026479605773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103495118005930017653070515 155242677008895026479605773)
  ·
    refine ⟨58216003878335634929852165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155242677008895026479605773 58216003878335634929852165)
    ·
      refine ⟨10915500727187931549347281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58216003878335634929852165 10915500727187931549347281)
      ·
        refine ⟨8186625545390948662010461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10915500727187931549347281 8186625545390948662010461)
        ·
          refine ⟨3069984579521605748253923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8186625545390948662010461 3069984579521605748253923)
          ·
            refine ⟨4604976869282408622380885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069984579521605748253923 4604976869282408622380885)
            ·
              refine ⟨26982286343451613021763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4604976869282408622380885 26982286343451613021763)
              ·
                rfl

theorem cell23_4256373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 9].length) (baseStart_4256373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256373 prefixEnd_4256373 := by exact prefixLift 4256373
  have htrace : WordTrace (prefixWord ++ tailWord_4256373) baseStart_4256373 baseEnd_4256373 := by
    simpa [prefixWord, tailWord_4256373, baseEnd_4256373] using wordTrace_append hprefix tailTrace_4256373
  have hstable : (prefixWord ++ tailWord_4256373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256373).length < 2 ^ (prefixWord ++ tailWord_4256373).sum := by decide
  have hdescent : baseEnd_4256373 < baseStart_4256373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256409 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_4256409 : Nat := 118140960795 + 4256409 * 2 ^ 59
def prefixEnd_4256409 : Nat := 4983230072969 + 3 ^ 40 * 4256409 * 2
def baseEnd_4256409 : Nat := 2185583679123142513912637

theorem tailTrace_4256409 : CollatzResearch.WordTrace tailWord_4256409 prefixEnd_4256409 2185583679123142513912637 := by
  unfold tailWord_4256409
  simp only [CollatzResearch.WordTrace]
  refine ⟨155243990036764604627916281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103495993357843069751944187 155243990036764604627916281)
  ·
    refine ⟨116432992527573453470937211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155243990036764604627916281 116432992527573453470937211)
    ·
      refine ⟨174649488791360180206405817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116432992527573453470937211 174649488791360180206405817)
      ·
        refine ⟨130987116593520135154804363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174649488791360180206405817 130987116593520135154804363)
        ·
          refine ⟨196480674890280202732206545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130987116593520135154804363 196480674890280202732206545)
          ·
            refine ⟨147360506167710152049154909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196480674890280202732206545 147360506167710152049154909)
            ·
              refine ⟨55260189812891307018433091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147360506167710152049154909 55260189812891307018433091)
              ·
                refine ⟨82890284719336960527649637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55260189812891307018433091 82890284719336960527649637)
                ·
                  refine ⟨15541928384875680098934307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82890284719336960527649637 15541928384875680098934307)
                  ·
                    refine ⟨23312892577313520148401461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15541928384875680098934307 23312892577313520148401461)
                    ·
                      refine ⟨2185583679123142513912637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23312892577313520148401461 2185583679123142513912637)
                      ·
                        rfl

theorem cell23_4256409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_4256409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256409 prefixEnd_4256409 := by exact prefixLift 4256409
  have htrace : WordTrace (prefixWord ++ tailWord_4256409) baseStart_4256409 baseEnd_4256409 := by
    simpa [prefixWord, tailWord_4256409, baseEnd_4256409] using wordTrace_append hprefix tailTrace_4256409
  have hstable : (prefixWord ++ tailWord_4256409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256409).length < 2 ^ (prefixWord ++ tailWord_4256409).sum := by decide
  have hdescent : baseEnd_4256409 < baseStart_4256409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256419 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_4256419 : Nat := 118140960795 + 4256419 * 2 ^ 59
def prefixEnd_4256419 : Nat := 4983230072969 + 3 ^ 40 * 4256419 * 2
def baseEnd_4256419 : Nat := 2185588813929687474787591

theorem tailTrace_4256419 : CollatzResearch.WordTrace tailWord_4256419 prefixEnd_4256419 2185588813929687474787591 := by
  unfold tailWord_4256419
  simp only [CollatzResearch.WordTrace]
  refine ⟨155244354766728376335780311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103496236511152250890520207 155244354766728376335780311)
  ·
    refine ⟨232866532150092564503670467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155244354766728376335780311 232866532150092564503670467)
    ·
      refine ⟨349299798225138846755505701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232866532150092564503670467 349299798225138846755505701)
      ·
        refine ⟨65493712167213533766657319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 349299798225138846755505701 65493712167213533766657319)
        ·
          refine ⟨98240568250820300649985979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65493712167213533766657319 98240568250820300649985979)
          ·
            refine ⟨147360852376230450974978969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98240568250820300649985979 147360852376230450974978969)
            ·
              refine ⟨110520639282172838231234227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147360852376230450974978969 110520639282172838231234227)
              ·
                refine ⟨165780958923259257346851341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110520639282172838231234227 165780958923259257346851341)
                ·
                  refine ⟨62167859596222221505069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165780958923259257346851341 62167859596222221505069253)
                  ·
                    refine ⟨11656473674291666532200485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62167859596222221505069253 11656473674291666532200485)
                    ·
                      refine ⟨2185588813929687474787591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11656473674291666532200485 2185588813929687474787591)
                      ·
                        rfl

theorem cell23_4256419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_4256419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256419 prefixEnd_4256419 := by exact prefixLift 4256419
  have htrace : WordTrace (prefixWord ++ tailWord_4256419) baseStart_4256419 baseEnd_4256419 := by
    simpa [prefixWord, tailWord_4256419, baseEnd_4256419] using wordTrace_append hprefix tailTrace_4256419
  have hstable : (prefixWord ++ tailWord_4256419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256419).length < 2 ^ (prefixWord ++ tailWord_4256419).sum := by decide
  have hdescent : baseEnd_4256419 < baseStart_4256419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256446 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_4256446 : Nat := 118140960795 + 4256446 * 2 ^ 59
def prefixEnd_4256446 : Nat := 4983230072969 + 3 ^ 40 * 4256446 * 2
def baseEnd_4256446 : Nat := 242844741989706541016663

theorem tailTrace_4256446 : CollatzResearch.WordTrace tailWord_4256446 prefixEnd_4256446 242844741989706541016663 := by
  unfold tailWord_4256446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19405667442203819993376649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103496893025087039964675461 19405667442203819993376649)
  ·
    refine ⟨14554250581652864995032487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19405667442203819993376649 14554250581652864995032487)
    ·
      refine ⟨21831375872479297492548731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14554250581652864995032487 21831375872479297492548731)
      ·
        refine ⟨32747063808718946238823097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21831375872479297492548731 32747063808718946238823097)
        ·
          refine ⟨24560297856539209679117323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32747063808718946238823097 24560297856539209679117323)
          ·
            refine ⟨36840446784808814518675985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24560297856539209679117323 36840446784808814518675985)
            ·
              refine ⟨27630335088606610889006989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36840446784808814518675985 27630335088606610889006989)
              ·
                refine ⟨10361375658227479083377621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27630335088606610889006989 10361375658227479083377621)
                ·
                  refine ⟨242844741989706541016663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10361375658227479083377621 242844741989706541016663)
                  ·
                    rfl

theorem cell23_4256446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_4256446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256446 prefixEnd_4256446 := by exact prefixLift 4256446
  have htrace : WordTrace (prefixWord ++ tailWord_4256446) baseStart_4256446 baseEnd_4256446 := by
    simpa [prefixWord, tailWord_4256446, baseEnd_4256446] using wordTrace_append hprefix tailTrace_4256446
  have hstable : (prefixWord ++ tailWord_4256446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256446).length < 2 ^ (prefixWord ++ tailWord_4256446).sum := by decide
  have hdescent : baseEnd_4256446 < baseStart_4256446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256456 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_4256456 : Nat := 118140960795 + 4256456 * 2 ^ 59
def prefixEnd_4256456 : Nat := 4983230072969 + 3 ^ 40 * 4256456 * 2
def baseEnd_4256456 : Nat := 2185607812713903830024921

theorem tailTrace_4256456 : CollatzResearch.WordTrace tailWord_4256456 prefixEnd_4256456 2185607812713903830024921 := by
  unfold tailWord_4256456
  simp only [CollatzResearch.WordTrace]
  refine ⟨77622852133797165827438611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103497136178396221103251481 77622852133797165827438611)
  ·
    refine ⟨116434278200695748741157917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77622852133797165827438611 116434278200695748741157917)
    ·
      refine ⟨43662854325260905777934219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116434278200695748741157917 43662854325260905777934219)
      ·
        refine ⟨65494281487891358666901329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43662854325260905777934219 65494281487891358666901329)
        ·
          refine ⟨49120711115918519000175997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65494281487891358666901329 49120711115918519000175997)
          ·
            refine ⟨18420266668469444625065999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49120711115918519000175997 18420266668469444625065999)
            ·
              refine ⟨27630400002704166937598999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18420266668469444625065999 27630400002704166937598999)
              ·
                refine ⟨41445600004056250406398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27630400002704166937598999 41445600004056250406398499)
                ·
                  refine ⟨62168400006084375609597749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41445600004056250406398499 62168400006084375609597749)
                  ·
                    refine ⟨5828287500570410213399789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62168400006084375609597749 5828287500570410213399789)
                    ·
                      refine ⟨2185607812713903830024921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828287500570410213399789 2185607812713903830024921)
                      ·
                        rfl

theorem cell23_4256456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_4256456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256456 prefixEnd_4256456 := by exact prefixLift 4256456
  have htrace : WordTrace (prefixWord ++ tailWord_4256456) baseStart_4256456 baseEnd_4256456 := by
    simpa [prefixWord, tailWord_4256456, baseEnd_4256456] using wordTrace_append hprefix tailTrace_4256456
  have hstable : (prefixWord ++ tailWord_4256456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256456).length < 2 ^ (prefixWord ++ tailWord_4256456).sum := by decide
  have hdescent : baseEnd_4256456 < baseStart_4256456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256496 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_4256496 : Nat := 118140960795 + 4256496 * 2 ^ 59
def prefixEnd_4256496 : Nat := 4983230072969 + 3 ^ 40 * 4256496 * 2
def baseEnd_4256496 : Nat := 2185628351940083673524737

theorem tailTrace_4256496 : CollatzResearch.WordTrace tailWord_4256496 prefixEnd_4256496 2185628351940083673524737 := by
  unfold tailWord_4256496
  simp only [CollatzResearch.WordTrace]
  refine ⟨77623581593724709243166671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103498108791632945657555561 77623581593724709243166671)
  ·
    refine ⟨116435372390587063864750007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77623581593724709243166671 116435372390587063864750007)
    ·
      refine ⟨174653058585880595797125011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116435372390587063864750007 174653058585880595797125011)
      ·
        refine ⟨261979587878820893695687517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174653058585880595797125011 261979587878820893695687517)
        ·
          refine ⟨98242345454557835135882819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261979587878820893695687517 98242345454557835135882819)
          ·
            refine ⟨147363518181836752703824229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98242345454557835135882819 147363518181836752703824229)
            ·
              refine ⟨27630659659094391131967043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147363518181836752703824229 27630659659094391131967043)
              ·
                refine ⟨41445989488641586697950565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27630659659094391131967043 41445989488641586697950565)
                ·
                  refine ⟨7771123029120297505865731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41445989488641586697950565 7771123029120297505865731)
                  ·
                    refine ⟨11656684543680446258798597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7771123029120297505865731 11656684543680446258798597)
                    ·
                      refine ⟨2185628351940083673524737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11656684543680446258798597 2185628351940083673524737)
                      ·
                        rfl

theorem cell23_4256496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_4256496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256496 prefixEnd_4256496 := by exact prefixLift 4256496
  have htrace : WordTrace (prefixWord ++ tailWord_4256496) baseStart_4256496 baseEnd_4256496 := by
    simpa [prefixWord, tailWord_4256496, baseEnd_4256496] using wordTrace_append hprefix tailTrace_4256496
  have hstable : (prefixWord ++ tailWord_4256496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256496).length < 2 ^ (prefixWord ++ tailWord_4256496).sum := by decide
  have hdescent : baseEnd_4256496 < baseStart_4256496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256526 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4256526 : Nat := 118140960795 + 4256526 * 2 ^ 59
def prefixEnd_4256526 : Nat := 4983230072969 + 3 ^ 40 * 4256526 * 2
def baseEnd_4256526 : Nat := 2185643756359718556149599

theorem tailTrace_4256526 : CollatzResearch.WordTrace tailWord_4256526 prefixEnd_4256526 2185643756359718556149599 := by
  unfold tailWord_4256526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406032172167591701240679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103498838251560489073283621 19406032172167591701240679)
  ·
    refine ⟨29109048258251387551861019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19406032172167591701240679 29109048258251387551861019)
    ·
      refine ⟨43663572387377081327791529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29109048258251387551861019 43663572387377081327791529)
      ·
        refine ⟨32747679290532810995843647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43663572387377081327791529 32747679290532810995843647)
        ·
          refine ⟨49121518935799216493765471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32747679290532810995843647 49121518935799216493765471)
          ·
            refine ⟨73682278403698824740648207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49121518935799216493765471 73682278403698824740648207)
            ·
              refine ⟨110523417605548237110972311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73682278403698824740648207 110523417605548237110972311)
              ·
                refine ⟨165785126408322355666458467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110523417605548237110972311 165785126408322355666458467)
                ·
                  refine ⟨248677689612483533499687701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165785126408322355666458467 248677689612483533499687701)
                  ·
                    refine ⟨11656766700585165632797861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 248677689612483533499687701 11656766700585165632797861)
                    ·
                      refine ⟨2185643756359718556149599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11656766700585165632797861 2185643756359718556149599)
                      ·
                        rfl

theorem cell23_4256526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4256526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256526 prefixEnd_4256526 := by exact prefixLift 4256526
  have htrace : WordTrace (prefixWord ++ tailWord_4256526) baseStart_4256526 baseEnd_4256526 := by
    simpa [prefixWord, tailWord_4256526, baseEnd_4256526] using wordTrace_append hprefix tailTrace_4256526
  have hstable : (prefixWord ++ tailWord_4256526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256526).length < 2 ^ (prefixWord ++ tailWord_4256526).sum := by decide
  have hdescent : baseEnd_4256526 < baseStart_4256526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256533 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_4256533 : Nat := 118140960795 + 4256533 * 2 ^ 59
def prefixEnd_4256533 : Nat := 4983230072969 + 3 ^ 40 * 4256533 * 2
def baseEnd_4256533 : Nat := 2185647350724300028762067

theorem tailTrace_4256533 : CollatzResearch.WordTrace tailWord_4256533 prefixEnd_4256533 2185647350724300028762067 := by
  unfold tailWord_4256533
  simp only [CollatzResearch.WordTrace]
  refine ⟨155248512688315373805430253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103499008458876915870286835 155248512688315373805430253)
  ·
    refine ⟨58218192258118265177036345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155248512688315373805430253 58218192258118265177036345)
    ·
      refine ⟨43663644193588698882777259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58218192258118265177036345 43663644193588698882777259)
      ·
        refine ⟨65495466290383048324165889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43663644193588698882777259 65495466290383048324165889)
        ·
          refine ⟨49121599717787286243124417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65495466290383048324165889 49121599717787286243124417)
          ·
            refine ⟨36841199788340464682343313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49121599717787286243124417 36841199788340464682343313)
            ·
              refine ⟨27630899841255348511757485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36841199788340464682343313 27630899841255348511757485)
              ·
                refine ⟨10361587440470755691909057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27630899841255348511757485 10361587440470755691909057)
                ·
                  refine ⟨7771190580353066768931793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10361587440470755691909057 7771190580353066768931793)
                  ·
                    refine ⟨5828392935264800076698845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7771190580353066768931793 5828392935264800076698845)
                    ·
                      refine ⟨2185647350724300028762067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828392935264800076698845 2185647350724300028762067)
                      ·
                        rfl

theorem cell23_4256533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_4256533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256533 prefixEnd_4256533 := by exact prefixLift 4256533
  have htrace : WordTrace (prefixWord ++ tailWord_4256533) baseStart_4256533 baseEnd_4256533 := by
    simpa [prefixWord, tailWord_4256533, baseEnd_4256533] using wordTrace_append hprefix tailTrace_4256533
  have hstable : (prefixWord ++ tailWord_4256533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256533).length < 2 ^ (prefixWord ++ tailWord_4256533).sum := by decide
  have hdescent : baseEnd_4256533 < baseStart_4256533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256597 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4256597 : Nat := 118140960795 + 4256597 * 2 ^ 59
def prefixEnd_4256597 : Nat := 4983230072969 + 3 ^ 40 * 4256597 * 2
def baseEnd_4256597 : Nat := 2185680213486187778361773

theorem tailTrace_4256597 : CollatzResearch.WordTrace tailWord_4256597 prefixEnd_4256597 2185680213486187778361773 := by
  unfold tailWord_4256597
  simp only [CollatzResearch.WordTrace]
  refine ⟨155250846960083512735760045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103500564640055675157173363 155250846960083512735760045)
  ·
    refine ⟨58219067610031317275910017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155250846960083512735760045 58219067610031317275910017)
    ·
      refine ⟨43664300707523487956932513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58219067610031317275910017 43664300707523487956932513)
      ·
        refine ⟨32748225530642615967699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43664300707523487956932513 32748225530642615967699385)
        ·
          refine ⟨24561169147981961975774539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32748225530642615967699385 24561169147981961975774539)
          ·
            refine ⟨36841753721972942963661809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24561169147981961975774539 36841753721972942963661809)
            ·
              refine ⟨27631315291479707222746357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36841753721972942963661809 27631315291479707222746357)
              ·
                refine ⟨2590435808576222552132471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27631315291479707222746357 2590435808576222552132471)
                ·
                  refine ⟨3885653712864333828198707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590435808576222552132471 3885653712864333828198707)
                  ·
                    refine ⟨5828480569296500742298061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885653712864333828198707 5828480569296500742298061)
                    ·
                      refine ⟨2185680213486187778361773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828480569296500742298061 2185680213486187778361773)
                      ·
                        rfl

theorem cell23_4256597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4256597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256597 prefixEnd_4256597 := by exact prefixLift 4256597
  have htrace : WordTrace (prefixWord ++ tailWord_4256597) baseStart_4256597 baseEnd_4256597 := by
    simpa [prefixWord, tailWord_4256597, baseEnd_4256597] using wordTrace_append hprefix tailTrace_4256597
  have hstable : (prefixWord ++ tailWord_4256597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256597).length < 2 ^ (prefixWord ++ tailWord_4256597).sum := by decide
  have hdescent : baseEnd_4256597 < baseStart_4256597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256613 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_4256613 : Nat := 118140960795 + 4256613 * 2 ^ 59
def prefixEnd_4256613 : Nat := 4983230072969 + 3 ^ 40 * 4256613 * 2
def baseEnd_4256613 : Nat := 728562809725553238587233

theorem tailTrace_4256613 : CollatzResearch.WordTrace tailWord_4256613 prefixEnd_4256613 728562809725553238587233 := by
  unfold tailWord_4256613
  simp only [CollatzResearch.WordTrace]
  refine ⟨155251430528025547468342493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103500953685350364978894995 155251430528025547468342493)
  ·
    refine ⟨58219286448009580300628435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155251430528025547468342493 58219286448009580300628435)
    ·
      refine ⟨87328929672014370450942653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58219286448009580300628435 87328929672014370450942653)
      ·
        refine ⟨32748348627005388919103495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87328929672014370450942653 32748348627005388919103495)
        ·
          refine ⟨49122522940508083378655243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32748348627005388919103495 49122522940508083378655243)
          ·
            refine ⟨73683784410762125067982865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49122522940508083378655243 73683784410762125067982865)
            ·
              refine ⟨55262838308071593800987149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73683784410762125067982865 55262838308071593800987149)
              ·
                refine ⟨20723564365526847675370181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55262838308071593800987149 20723564365526847675370181)
                ·
                  refine ⟨3885668318536283939131909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20723564365526847675370181 3885668318536283939131909)
                  ·
                    refine ⟨728562809725553238587233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885668318536283939131909 728562809725553238587233)
                    ·
                      rfl

theorem cell23_4256613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_4256613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256613 prefixEnd_4256613 := by exact prefixLift 4256613
  have htrace : WordTrace (prefixWord ++ tailWord_4256613) baseStart_4256613 baseEnd_4256613 := by
    simpa [prefixWord, tailWord_4256613, baseEnd_4256613] using wordTrace_append hprefix tailTrace_4256613
  have hstable : (prefixWord ++ tailWord_4256613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256613).length < 2 ^ (prefixWord ++ tailWord_4256613).sum := by decide
  have hdescent : baseEnd_4256613 < baseStart_4256613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256630 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_4256630 : Nat := 118140960795 + 4256630 * 2 ^ 59
def prefixEnd_4256630 : Nat := 4983230072969 + 3 ^ 40 * 4256630 * 2
def baseEnd_4256630 : Nat := 728565719449262049749707

theorem tailTrace_4256630 : CollatzResearch.WordTrace tailWord_4256630 prefixEnd_4256630 728565719449262049749707 := by
  unfold tailWord_4256630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703253160560247460731959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103501367045975972914474229 9703253160560247460731959)
  ·
    refine ⟨14554879740840371191097939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9703253160560247460731959 14554879740840371191097939)
    ·
      refine ⟨21832319611260556786646909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14554879740840371191097939 21832319611260556786646909)
      ·
        refine ⟨8187119854222708794992591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21832319611260556786646909 8187119854222708794992591)
        ·
          refine ⟨12280679781334063192488887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187119854222708794992591 12280679781334063192488887)
          ·
            refine ⟨18421019672001094788733331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12280679781334063192488887 18421019672001094788733331)
            ·
              refine ⟨27631529508001642183099997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18421019672001094788733331 27631529508001642183099997)
              ·
                refine ⟨10361823565500615818662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27631529508001642183099997 10361823565500615818662499)
                ·
                  refine ⟨15542735348250923727993749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361823565500615818662499 15542735348250923727993749)
                  ·
                    refine ⟨728565719449262049749707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15542735348250923727993749 728565719449262049749707)
                    ·
                      rfl

theorem cell23_4256630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_4256630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256630 prefixEnd_4256630 := by exact prefixLift 4256630
  have htrace : WordTrace (prefixWord ++ tailWord_4256630) baseStart_4256630 baseEnd_4256630 := by
    simpa [prefixWord, tailWord_4256630, baseEnd_4256630] using wordTrace_append hprefix tailTrace_4256630
  have hstable : (prefixWord ++ tailWord_4256630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256630).length < 2 ^ (prefixWord ++ tailWord_4256630).sum := by decide
  have hdescent : baseEnd_4256630 < baseStart_4256630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256633 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_4256633 : Nat := 118140960795 + 4256633 * 2 ^ 59
def prefixEnd_4256633 : Nat := 4983230072969 + 3 ^ 40 * 4256633 * 2
def baseEnd_4256633 : Nat := 2185698698789749637511607

theorem tailTrace_4256633 : CollatzResearch.WordTrace tailWord_4256633 prefixEnd_4256633 2185698698789749637511607 := by
  unfold tailWord_4256633
  simp only [CollatzResearch.WordTrace]
  refine ⟨155252159987953090884070553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103501439991968727256047035 155252159987953090884070553)
  ·
    refine ⟨116439119990964818163052915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155252159987953090884070553 116439119990964818163052915)
    ·
      refine ⟨174658679986447227244579373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116439119990964818163052915 174658679986447227244579373)
      ·
        refine ⟨65497004994917710216717265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174658679986447227244579373 65497004994917710216717265)
        ·
          refine ⟨49122753746188282662537949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65497004994917710216717265 49122753746188282662537949)
          ·
            refine ⟨18421032654820605998451731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49122753746188282662537949 18421032654820605998451731)
            ·
              refine ⟨27631548982230908997677597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18421032654820605998451731 27631548982230908997677597)
              ·
                refine ⟨10361830868336590874129099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27631548982230908997677597 10361830868336590874129099)
                ·
                  refine ⟨15542746302504886311193649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361830868336590874129099 15542746302504886311193649)
                  ·
                    refine ⟨11657059726878664733395237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15542746302504886311193649 11657059726878664733395237)
                    ·
                      refine ⟨2185698698789749637511607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11657059726878664733395237 2185698698789749637511607)
                      ·
                        rfl

theorem cell23_4256633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_4256633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256633 prefixEnd_4256633 := by exact prefixLift 4256633
  have htrace : WordTrace (prefixWord ++ tailWord_4256633) baseStart_4256633 baseEnd_4256633 := by
    simpa [prefixWord, tailWord_4256633, baseEnd_4256633] using wordTrace_append hprefix tailTrace_4256633
  have hstable : (prefixWord ++ tailWord_4256633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256633).length < 2 ^ (prefixWord ++ tailWord_4256633).sum := by decide
  have hdescent : baseEnd_4256633 < baseStart_4256633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4256636 : Nat := 118140960795 + 4256636 * 2 ^ 59
def prefixEnd_4256636 : Nat := 4983230072969 + 3 ^ 40 * 4256636 * 2
def baseEnd_4256636 : Nat := 2185700239231713125774093

theorem tailTrace_4256636 : CollatzResearch.WordTrace tailWord_4256636 prefixEnd_4256636 2185700239231713125774093 := by
  unfold tailWord_4256636
  simp only [CollatzResearch.WordTrace]
  refine ⟨77626134703471111198214881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103501512937961481597619841 77626134703471111198214881)
  ·
    refine ⟨58219601027603333398661161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77626134703471111198214881 58219601027603333398661161)
    ·
      refine ⟨43664700770702500048995871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58219601027603333398661161 43664700770702500048995871)
      ·
        refine ⟨65497051156053750073493807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43664700770702500048995871 65497051156053750073493807)
        ·
          refine ⟨98245576734080625110240711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65497051156053750073493807 98245576734080625110240711)
          ·
            refine ⟨147368365101120937665361067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98245576734080625110240711 147368365101120937665361067)
            ·
              refine ⟨221052547651681406498041601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147368365101120937665361067 221052547651681406498041601)
              ·
                refine ⟨165789410738761054873531201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221052547651681406498041601 165789410738761054873531201)
                ·
                  refine ⟨124342058054070791155148401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165789410738761054873531201 124342058054070791155148401)
                  ·
                    refine ⟨93256543540553093366361301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124342058054070791155148401 93256543540553093366361301)
                    ·
                      refine ⟨2185700239231713125774093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93256543540553093366361301 2185700239231713125774093)
                      ·
                        rfl

theorem cell23_4256636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4256636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256636 prefixEnd_4256636 := by exact prefixLift 4256636
  have htrace : WordTrace (prefixWord ++ tailWord_4256636) baseStart_4256636 baseEnd_4256636 := by
    simpa [prefixWord, tailWord_4256636, baseEnd_4256636] using wordTrace_append hprefix tailTrace_4256636
  have hstable : (prefixWord ++ tailWord_4256636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256636).length < 2 ^ (prefixWord ++ tailWord_4256636).sum := by decide
  have hdescent : baseEnd_4256636 < baseStart_4256636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256643 : List Nat := [1, 1, 1, 3, 4, 1, 5, 7]
def baseStart_4256643 : Nat := 118140960795 + 4256643 * 2 ^ 59
def prefixEnd_4256643 : Nat := 4983230072969 + 3 ^ 40 * 4256643 * 2
def baseEnd_4256643 : Nat := 80951993836899799940243

theorem tailTrace_4256643 : CollatzResearch.WordTrace tailWord_4256643 prefixEnd_4256643 80951993836899799940243 := by
  unfold tailWord_4256643
  simp only [CollatzResearch.WordTrace]
  refine ⟨155252524717916862591934583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103501683145277908394623055 155252524717916862591934583)
  ·
    refine ⟨232878787076875293887901875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155252524717916862591934583 232878787076875293887901875)
    ·
      refine ⟨349318180615312940831852813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232878787076875293887901875 349318180615312940831852813)
      ·
        refine ⟨130994317730742352811944805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349318180615312940831852813 130994317730742352811944805)
        ·
          refine ⟨24561434574514191152239651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130994317730742352811944805 24561434574514191152239651)
          ·
            refine ⟨36842151861771286728359477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24561434574514191152239651 36842151861771286728359477)
            ·
              refine ⟨3453951737041058130783701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36842151861771286728359477 3453951737041058130783701)
              ·
                refine ⟨80951993836899799940243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3453951737041058130783701 80951993836899799940243)
                ·
                  rfl

theorem cell23_4256643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 7].length) (baseStart_4256643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256643 prefixEnd_4256643 := by exact prefixLift 4256643
  have htrace : WordTrace (prefixWord ++ tailWord_4256643) baseStart_4256643 baseEnd_4256643 := by
    simpa [prefixWord, tailWord_4256643, baseEnd_4256643] using wordTrace_append hprefix tailTrace_4256643
  have hstable : (prefixWord ++ tailWord_4256643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256643).length < 2 ^ (prefixWord ++ tailWord_4256643).sum := by decide
  have hdescent : baseEnd_4256643 < baseStart_4256643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256650 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4256650 : Nat := 118140960795 + 4256650 * 2 ^ 59
def prefixEnd_4256650 : Nat := 4983230072969 + 3 ^ 40 * 4256650 * 2
def baseEnd_4256650 : Nat := 2185707427960876070999029

theorem tailTrace_4256650 : CollatzResearch.WordTrace tailWord_4256650 prefixEnd_4256650 2185707427960876070999029 := by
  unfold tailWord_4256650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813195007222875696859851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103501853352594335191626269 38813195007222875696859851)
  ·
    refine ⟨58219792510834313545289777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38813195007222875696859851 58219792510834313545289777)
    ·
      refine ⟨43664844383125735158967333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58219792510834313545289777 43664844383125735158967333)
      ·
        refine ⟨8187158321836075342306375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43664844383125735158967333 8187158321836075342306375)
        ·
          refine ⟨12280737482754113013459563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187158321836075342306375 12280737482754113013459563)
          ·
            refine ⟨18421106224131169520189345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12280737482754113013459563 18421106224131169520189345)
            ·
              refine ⟨13815829668098377140142009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18421106224131169520189345 13815829668098377140142009)
              ·
                refine ⟨10361872251073782855106507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13815829668098377140142009 10361872251073782855106507)
                ·
                  refine ⟨15542808376610674282659761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361872251073782855106507 15542808376610674282659761)
                  ·
                    refine ⟨11657106282458005711994821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15542808376610674282659761 11657106282458005711994821)
                    ·
                      refine ⟨2185707427960876070999029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11657106282458005711994821 2185707427960876070999029)
                      ·
                        rfl

theorem cell23_4256650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4256650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256650 prefixEnd_4256650 := by exact prefixLift 4256650
  have htrace : WordTrace (prefixWord ++ tailWord_4256650) baseStart_4256650 baseEnd_4256650 := by
    simpa [prefixWord, tailWord_4256650, baseEnd_4256650] using wordTrace_append hprefix tailTrace_4256650
  have hstable : (prefixWord ++ tailWord_4256650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256650).length < 2 ^ (prefixWord ++ tailWord_4256650).sum := by decide
  have hdescent : baseEnd_4256650 < baseStart_4256650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256694 : List Nat := [5, 1, 4, 1, 1, 1, 1, 9]
def baseStart_4256694 : Nat := 118140960795 + 4256694 * 2 ^ 59
def prefixEnd_4256694 : Nat := 4983230072969 + 3 ^ 40 * 4256694 * 2
def baseEnd_4256694 : Nat := 80952963744802736994401

theorem tailTrace_4256694 : CollatzResearch.WordTrace tailWord_4256694 prefixEnd_4256694 80952963744802736994401 := by
  unfold tailWord_4256694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703399052545756143877571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103502923227154732201360757 9703399052545756143877571)
  ·
    refine ⟨14555098578818634215816357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9703399052545756143877571 14555098578818634215816357)
    ·
      refine ⟨2729080983528493915465567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14555098578818634215816357 2729080983528493915465567)
      ·
        refine ⟨4093621475292740873198351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729080983528493915465567 4093621475292740873198351)
        ·
          refine ⟨6140432212939111309797527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093621475292740873198351 6140432212939111309797527)
          ·
            refine ⟨9210648319408666964696291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140432212939111309797527 9210648319408666964696291)
            ·
              refine ⟨13815972479113000447044437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9210648319408666964696291 13815972479113000447044437)
              ·
                refine ⟨80952963744802736994401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13815972479113000447044437 80952963744802736994401)
                ·
                  rfl

theorem cell23_4256694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_4256694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256694 prefixEnd_4256694 := by exact prefixLift 4256694
  have htrace : WordTrace (prefixWord ++ tailWord_4256694) baseStart_4256694 baseEnd_4256694 := by
    simpa [prefixWord, tailWord_4256694, baseEnd_4256694] using wordTrace_append hprefix tailTrace_4256694
  have hstable : (prefixWord ++ tailWord_4256694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256694).length < 2 ^ (prefixWord ++ tailWord_4256694).sum := by decide
  have hdescent : baseEnd_4256694 < baseStart_4256694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256697 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4256697 : Nat := 118140960795 + 4256697 * 2 ^ 59
def prefixEnd_4256697 : Nat := 4983230072969 + 3 ^ 40 * 4256697 * 2
def baseEnd_4256697 : Nat := 2185731561551637387111313

theorem tailTrace_4256697 : CollatzResearch.WordTrace tailWord_4256697 prefixEnd_4256697 2185731561551637387111313 := by
  unfold tailWord_4256697
  simp only [CollatzResearch.WordTrace]
  refine ⟨155254494259721229814400345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103502996173147486542933563 155254494259721229814400345)
  ·
    refine ⟨116440870694790922360800259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155254494259721229814400345 116440870694790922360800259)
    ·
      refine ⟨174661306042186383541200389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116440870694790922360800259 174661306042186383541200389)
      ·
        refine ⟨32748994882909946913975073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174661306042186383541200389 32748994882909946913975073)
        ·
          refine ⟨24561746162182460185481305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32748994882909946913975073 24561746162182460185481305)
          ·
            refine ⟨18421309621636845139110979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24561746162182460185481305 18421309621636845139110979)
            ·
              refine ⟨27631964432455267708666469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18421309621636845139110979 27631964432455267708666469)
              ·
                refine ⟨5180993331085362695374963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27631964432455267708666469 5180993331085362695374963)
                ·
                  refine ⟨7771489996628044043062445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5180993331085362695374963 7771489996628044043062445)
                  ·
                    refine ⟨2914308748735516516148417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7771489996628044043062445 2914308748735516516148417)
                    ·
                      refine ⟨2185731561551637387111313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914308748735516516148417 2185731561551637387111313)
                      ·
                        rfl

theorem cell23_4256697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4256697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256697 prefixEnd_4256697 := by exact prefixLift 4256697
  have htrace : WordTrace (prefixWord ++ tailWord_4256697) baseStart_4256697 baseEnd_4256697 := by
    simpa [prefixWord, tailWord_4256697, baseEnd_4256697] using wordTrace_append hprefix tailTrace_4256697
  have hstable : (prefixWord ++ tailWord_4256697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256697).length < 2 ^ (prefixWord ++ tailWord_4256697).sum := by decide
  have hdescent : baseEnd_4256697 < baseStart_4256697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256738 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4256738 : Nat := 118140960795 + 4256738 * 2 ^ 59
def prefixEnd_4256738 : Nat := 4983230072969 + 3 ^ 40 * 4256738 * 2
def baseEnd_4256738 : Nat := 2185752614258471726698625

theorem tailTrace_4256738 : CollatzResearch.WordTrace tailWord_4256738 prefixEnd_4256738 2185752614258471726698625 := by
  unfold tailWord_4256738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813997413143173454160717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103503993101715129211095245 38813997413143173454160717)
  ·
    refine ⟨14555249029928690045310269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38813997413143173454160717 14555249029928690045310269)
    ·
      refine ⟨5458218386223258766991351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14555249029928690045310269 5458218386223258766991351)
      ·
        refine ⟨8187327579334888150487027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458218386223258766991351 8187327579334888150487027)
        ·
          refine ⟨12280991369002332225730541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187327579334888150487027 12280991369002332225730541)
          ·
            refine ⟨4605371763375874584648953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12280991369002332225730541 4605371763375874584648953)
            ·
              refine ⟨3454028822531905938486715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605371763375874584648953 3454028822531905938486715)
              ·
                refine ⟨5181043233797858907730073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454028822531905938486715 5181043233797858907730073)
                ·
                  refine ⟨3885782425348394180797555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5181043233797858907730073 3885782425348394180797555)
                  ·
                    refine ⟨5828673638022591271196333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885782425348394180797555 5828673638022591271196333)
                    ·
                      refine ⟨2185752614258471726698625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828673638022591271196333 2185752614258471726698625)
                      ·
                        rfl

theorem cell23_4256738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4256738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256738 prefixEnd_4256738 := by exact prefixLift 4256738
  have htrace : WordTrace (prefixWord ++ tailWord_4256738) baseStart_4256738 baseEnd_4256738 := by
    simpa [prefixWord, tailWord_4256738, baseEnd_4256738] using wordTrace_append hprefix tailTrace_4256738
  have hstable : (prefixWord ++ tailWord_4256738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256738).length < 2 ^ (prefixWord ++ tailWord_4256738).sum := by decide
  have hdescent : baseEnd_4256738 < baseStart_4256738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256773 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4256773 : Nat := 118140960795 + 4256773 * 2 ^ 59
def prefixEnd_4256773 : Nat := 4983230072969 + 3 ^ 40 * 4256773 * 2
def baseEnd_4256773 : Nat := 2185770586081379089760963

theorem tailTrace_4256773 : CollatzResearch.WordTrace tailWord_4256773 prefixEnd_4256773 2185770586081379089760963 := by
  unfold tailWord_4256773
  simp only [CollatzResearch.WordTrace]
  refine ⟨155257266207445894794166973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103504844138297263196111315 155257266207445894794166973)
  ·
    refine ⟨58221474827792210547812615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155257266207445894794166973 58221474827792210547812615)
    ·
      refine ⟨87332212241688315821718923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58221474827792210547812615 87332212241688315821718923)
      ·
        refine ⟨130998318362532473732578385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87332212241688315821718923 130998318362532473732578385)
        ·
          refine ⟨98248738771899355299433789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130998318362532473732578385 98248738771899355299433789)
          ·
            refine ⟨36843277039462258237287671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98248738771899355299433789 36843277039462258237287671)
            ·
              refine ⟨55264915559193387355931507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36843277039462258237287671 55264915559193387355931507)
              ·
                refine ⟨82897373338790081033897261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55264915559193387355931507 82897373338790081033897261)
                ·
                  refine ⟨31086515002046280387711473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82897373338790081033897261 31086515002046280387711473)
                  ·
                    refine ⟨23314886251534710290783605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31086515002046280387711473 23314886251534710290783605)
                    ·
                      refine ⟨2185770586081379089760963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23314886251534710290783605 2185770586081379089760963)
                      ·
                        rfl

theorem cell23_4256773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4256773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256773 prefixEnd_4256773 := by exact prefixLift 4256773
  have htrace : WordTrace (prefixWord ++ tailWord_4256773) baseStart_4256773 baseEnd_4256773 := by
    simpa [prefixWord, tailWord_4256773, baseEnd_4256773] using wordTrace_append hprefix tailTrace_4256773
  have hstable : (prefixWord ++ tailWord_4256773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256773).length < 2 ^ (prefixWord ++ tailWord_4256773).sum := by decide
  have hdescent : baseEnd_4256773 < baseStart_4256773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256780 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_4256780 : Nat := 118140960795 + 4256780 * 2 ^ 59
def prefixEnd_4256780 : Nat := 4983230072969 + 3 ^ 40 * 4256780 * 2
def baseEnd_4256780 : Nat := 728591393481986854124477

theorem tailTrace_4256780 : CollatzResearch.WordTrace tailWord_4256780 prefixEnd_4256780 728591393481986854124477 := by
  unfold tailWord_4256780
  simp only [CollatzResearch.WordTrace]
  refine ⟨77628760759210267494835897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103505014345613689993114529 77628760759210267494835897)
  ·
    refine ⟨58221570569407700621126923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77628760759210267494835897 58221570569407700621126923)
    ·
      refine ⟨87332355854111550931690385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58221570569407700621126923 87332355854111550931690385)
      ·
        refine ⟨65499266890583663198767789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87332355854111550931690385 65499266890583663198767789)
        ·
          refine ⟨24562225083968873699537921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65499266890583663198767789 24562225083968873699537921)
          ·
            refine ⟨18421668812976655274653441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24562225083968873699537921 18421668812976655274653441)
            ·
              refine ⟨13816251609732491455990081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18421668812976655274653441 13816251609732491455990081)
              ·
                refine ⟨10362188707299368591992561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13816251609732491455990081 10362188707299368591992561)
                ·
                  refine ⟨7771641530474526443994421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10362188707299368591992561 7771641530474526443994421)
                  ·
                    refine ⟨728591393481986854124477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7771641530474526443994421 728591393481986854124477)
                    ·
                      rfl

theorem cell23_4256780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_4256780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256780 prefixEnd_4256780 := by exact prefixLift 4256780
  have htrace : WordTrace (prefixWord ++ tailWord_4256780) baseStart_4256780 baseEnd_4256780 := by
    simpa [prefixWord, tailWord_4256780, baseEnd_4256780] using wordTrace_append hprefix tailTrace_4256780
  have hstable : (prefixWord ++ tailWord_4256780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256780).length < 2 ^ (prefixWord ++ tailWord_4256780).sum := by decide
  have hdescent : baseEnd_4256780 < baseStart_4256780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256823 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 8]
def baseStart_4256823 : Nat := 118140960795 + 4256823 * 2 ^ 59
def prefixEnd_4256823 : Nat := 4983230072969 + 3 ^ 40 * 4256823 * 2
def baseEnd_4256823 : Nat := 242866251123789321570637

theorem tailTrace_4256823 : CollatzResearch.WordTrace tailWord_4256823 prefixEnd_4256823 242866251123789321570637 := by
  unfold tailWord_4256823
  simp only [CollatzResearch.WordTrace]
  refine ⟨155259089857264753333487123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103506059904843168888991415 155259089857264753333487123)
  ·
    refine ⟨232888634785897130000230685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155259089857264753333487123 232888634785897130000230685)
    ·
      refine ⟨87333238044711423750086507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232888634785897130000230685 87333238044711423750086507)
      ·
        refine ⟨130999857067067135625129761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87333238044711423750086507 130999857067067135625129761)
        ·
          refine ⟨98249892800300351718847321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130999857067067135625129761 98249892800300351718847321)
          ·
            refine ⟨73687419600225263789135491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98249892800300351718847321 73687419600225263789135491)
            ·
              refine ⟨110531129400337895683703237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73687419600225263789135491 110531129400337895683703237)
              ·
                refine ⟨20724586762563355440694357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110531129400337895683703237 20724586762563355440694357)
                ·
                  refine ⟨242866251123789321570637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20724586762563355440694357 242866251123789321570637)
                  ·
                    rfl

theorem cell23_4256823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 8].length) (baseStart_4256823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256823 prefixEnd_4256823 := by exact prefixLift 4256823
  have htrace : WordTrace (prefixWord ++ tailWord_4256823) baseStart_4256823 baseEnd_4256823 := by
    simpa [prefixWord, tailWord_4256823, baseEnd_4256823] using wordTrace_append hprefix tailTrace_4256823
  have hstable : (prefixWord ++ tailWord_4256823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256823).length < 2 ^ (prefixWord ++ tailWord_4256823).sum := by decide
  have hdescent : baseEnd_4256823 < baseStart_4256823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256860 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4256860 : Nat := 118140960795 + 4256860 * 2 ^ 59
def prefixEnd_4256860 : Nat := 4983230072969 + 3 ^ 40 * 4256860 * 2
def baseEnd_4256860 : Nat := 2185815258898320249373063

theorem tailTrace_4256860 : CollatzResearch.WordTrace tailWord_4256860 prefixEnd_4256860 2185815258898320249373063 := by
  unfold tailWord_4256860
  simp only [CollatzResearch.WordTrace]
  refine ⟨77630219679065354326292017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103506959572087139101722689 77630219679065354326292017)
  ·
    refine ⟨58222664759299015744719013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77630219679065354326292017 58222664759299015744719013)
    ·
      refine ⟨10916749642368565452134815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58222664759299015744719013 10916749642368565452134815)
      ·
        refine ⟨16375124463552848178202223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916749642368565452134815 16375124463552848178202223)
        ·
          refine ⟨24562686695329272267303335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16375124463552848178202223 24562686695329272267303335)
          ·
            refine ⟨36844030042993908400955003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24562686695329272267303335 36844030042993908400955003)
            ·
              refine ⟨55266045064490862601432505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36844030042993908400955003 55266045064490862601432505)
              ·
                refine ⟨41449533798368146951074379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55266045064490862601432505 41449533798368146951074379)
                ·
                  refine ⟨62174300697552220426611569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41449533798368146951074379 62174300697552220426611569)
                  ·
                    refine ⟨46630725523164165319958677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62174300697552220426611569 46630725523164165319958677)
                    ·
                      refine ⟨2185815258898320249373063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46630725523164165319958677 2185815258898320249373063)
                      ·
                        rfl

theorem cell23_4256860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4256860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256860 prefixEnd_4256860 := by exact prefixLift 4256860
  have htrace : WordTrace (prefixWord ++ tailWord_4256860) baseStart_4256860 baseEnd_4256860 := by
    simpa [prefixWord, tailWord_4256860, baseEnd_4256860] using wordTrace_append hprefix tailTrace_4256860
  have hstable : (prefixWord ++ tailWord_4256860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256860).length < 2 ^ (prefixWord ++ tailWord_4256860).sum := by decide
  have hdescent : baseEnd_4256860 < baseStart_4256860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256901 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_4256901 : Nat := 118140960795 + 4256901 * 2 ^ 59
def prefixEnd_4256901 : Nat := 4983230072969 + 3 ^ 40 * 4256901 * 2
def baseEnd_4256901 : Nat := 2185836311605154588960375

theorem tailTrace_4256901 : CollatzResearch.WordTrace tailWord_4256901 prefixEnd_4256901 2185836311605154588960375 := by
  unfold tailWord_4256901
  simp only [CollatzResearch.WordTrace]
  refine ⟨155261934750982172654826557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103507956500654781769884371 155261934750982172654826557)
  ·
    refine ⟨58223225531618314745559959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155261934750982172654826557 58223225531618314745559959)
    ·
      refine ⟨87334838297427472118339939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58223225531618314745559959 87334838297427472118339939)
      ·
        refine ⟨131002257446141208177509909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87334838297427472118339939 131002257446141208177509909)
        ·
          refine ⟨6140730817787869133320777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131002257446141208177509909 6140730817787869133320777)
          ·
            refine ⟨4605548113340901849990583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6140730817787869133320777 4605548113340901849990583)
            ·
              refine ⟨6908322170011352774985875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605548113340901849990583 6908322170011352774985875)
              ·
                refine ⟨10362483255017029162478813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6908322170011352774985875 10362483255017029162478813)
                ·
                  refine ⟨3885931220631385935929555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10362483255017029162478813 3885931220631385935929555)
                  ·
                    refine ⟨5828896830947078903894333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885931220631385935929555 5828896830947078903894333)
                    ·
                      refine ⟨2185836311605154588960375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5828896830947078903894333 2185836311605154588960375)
                      ·
                        rfl

theorem cell23_4256901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_4256901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256901 prefixEnd_4256901 := by exact prefixLift 4256901
  have htrace : WordTrace (prefixWord ++ tailWord_4256901) baseStart_4256901 baseEnd_4256901 := by
    simpa [prefixWord, tailWord_4256901, baseEnd_4256901] using wordTrace_append hprefix tailTrace_4256901
  have hstable : (prefixWord ++ tailWord_4256901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256901).length < 2 ^ (prefixWord ++ tailWord_4256901).sum := by decide
  have hdescent : baseEnd_4256901 < baseStart_4256901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256924 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4256924 : Nat := 118140960795 + 4256924 * 2 ^ 59
def prefixEnd_4256924 : Nat := 4983230072969 + 3 ^ 40 * 4256924 * 2
def baseEnd_4256924 : Nat := 2185848121660207998972769

theorem tailTrace_4256924 : CollatzResearch.WordTrace tailWord_4256924 prefixEnd_4256924 2185848121660207998972769 := by
  unfold tailWord_4256924
  simp only [CollatzResearch.WordTrace]
  refine ⟨77631386814949423791456913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103508515753265898388609217 77631386814949423791456913)
  ·
    refine ⟨58223540111212067843592685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77631386814949423791456913 58223540111212067843592685)
    ·
      refine ⟨21833827541704525441347257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58223540111212067843592685 21833827541704525441347257)
      ·
        refine ⟨16375370656278394081010443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21833827541704525441347257 16375370656278394081010443)
        ·
          refine ⟨24563055984417591121515665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16375370656278394081010443 24563055984417591121515665)
          ·
            refine ⟨18422291988313193341136749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24563055984417591121515665 18422291988313193341136749)
            ·
              refine ⟨6908359495617447502926281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18422291988313193341136749 6908359495617447502926281)
              ·
                refine ⟨5181269621713085627194711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6908359495617447502926281 5181269621713085627194711)
                ·
                  refine ⟨7771904432569628440792067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181269621713085627194711 7771904432569628440792067)
                  ·
                    refine ⟨11657856648854442661188101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7771904432569628440792067 11657856648854442661188101)
                    ·
                      refine ⟨2185848121660207998972769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11657856648854442661188101 2185848121660207998972769)
                      ·
                        rfl

theorem cell23_4256924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4256924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256924 prefixEnd_4256924 := by exact prefixLift 4256924
  have htrace : WordTrace (prefixWord ++ tailWord_4256924) baseStart_4256924 baseEnd_4256924 := by
    simpa [prefixWord, tailWord_4256924, baseEnd_4256924] using wordTrace_append hprefix tailTrace_4256924
  have hstable : (prefixWord ++ tailWord_4256924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256924).length < 2 ^ (prefixWord ++ tailWord_4256924).sum := by decide
  have hdescent : baseEnd_4256924 < baseStart_4256924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4256964 : List Nat := [2, 3, 3, 1, 3, 2, 1, 8]
def baseStart_4256964 : Nat := 118140960795 + 4256964 * 2 ^ 59
def prefixEnd_4256964 : Nat := 4983230072969 + 3 ^ 40 * 4256964 * 2
def baseEnd_4256964 : Nat := 80958098551347697869355

theorem tailTrace_4256964 : CollatzResearch.WordTrace tailWord_4256964 prefixEnd_4256964 80958098551347697869355 := by
  unfold tailWord_4256964
  simp only [CollatzResearch.WordTrace]
  refine ⟨77632116274876967207184973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103509488366502622942913297 77632116274876967207184973)
  ·
    refine ⟨29112043603078862702694365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77632116274876967207184973 29112043603078862702694365)
    ·
      refine ⟨10917016351154573513510387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29112043603078862702694365 10917016351154573513510387)
      ·
        refine ⟨16375524526731860270265581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10917016351154573513510387 16375524526731860270265581)
        ·
          refine ⟨6140821697524447601349593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16375524526731860270265581 6140821697524447601349593)
          ·
            refine ⟨4605616273143335701012195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6140821697524447601349593 4605616273143335701012195)
            ·
              refine ⟨6908424409715003551518293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605616273143335701012195 6908424409715003551518293)
              ·
                refine ⟨80958098551347697869355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6908424409715003551518293 80958098551347697869355)
                ·
                  rfl

theorem cell23_4256964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 8].length) (baseStart_4256964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4256964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4256964 prefixEnd_4256964 := by exact prefixLift 4256964
  have htrace : WordTrace (prefixWord ++ tailWord_4256964) baseStart_4256964 baseEnd_4256964 := by
    simpa [prefixWord, tailWord_4256964, baseEnd_4256964] using wordTrace_append hprefix tailTrace_4256964
  have hstable : (prefixWord ++ tailWord_4256964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4256964).length < 2 ^ (prefixWord ++ tailWord_4256964).sum := by decide
  have hdescent : baseEnd_4256964 < baseStart_4256964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4256964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257027 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_4257027 : Nat := 118140960795 + 4257027 * 2 ^ 59
def prefixEnd_4257027 : Nat := 4983230072969 + 3 ^ 40 * 4257027 * 2
def baseEnd_4257027 : Nat := 2185901010167621095984795

theorem tailTrace_4257027 : CollatzResearch.WordTrace tailWord_4257027 prefixEnd_4257027 2185901010167621095984795 := by
  unfold tailWord_4257027
  simp only [CollatzResearch.WordTrace]
  refine ⟨155266530348525696173913335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103511020232350464115942223 155266530348525696173913335)
  ·
    refine ⟨232899795522788544260870003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155266530348525696173913335 232899795522788544260870003)
    ·
      refine ⟨349349693284182816391305005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232899795522788544260870003 349349693284182816391305005)
      ·
        refine ⟨131006134981568556146739377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349349693284182816391305005 131006134981568556146739377)
        ·
          refine ⟨98254601236176417110054533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131006134981568556146739377 98254601236176417110054533)
          ·
            refine ⟨18422737731783078208135225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98254601236176417110054533 18422737731783078208135225)
            ·
              refine ⟨13817053298837308656101419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18422737731783078208135225 13817053298837308656101419)
              ·
                refine ⟨20725579948255962984152129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13817053298837308656101419 20725579948255962984152129)
                ·
                  refine ⟨15544184961191972238114097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20725579948255962984152129 15544184961191972238114097)
                  ·
                    refine ⟨11658138720893979178585573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15544184961191972238114097 11658138720893979178585573)
                    ·
                      refine ⟨2185901010167621095984795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11658138720893979178585573 2185901010167621095984795)
                      ·
                        rfl

theorem cell23_4257027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_4257027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257027 prefixEnd_4257027 := by exact prefixLift 4257027
  have htrace : WordTrace (prefixWord ++ tailWord_4257027) baseStart_4257027 baseEnd_4257027 := by
    simpa [prefixWord, tailWord_4257027, baseEnd_4257027] using wordTrace_append hprefix tailTrace_4257027
  have hstable : (prefixWord ++ tailWord_4257027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257027).length < 2 ^ (prefixWord ++ tailWord_4257027).sum := by decide
  have hdescent : baseEnd_4257027 < baseStart_4257027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_4257040 : Nat := 118140960795 + 4257040 * 2 ^ 59
def prefixEnd_4257040 : Nat := 4983230072969 + 3 ^ 40 * 4257040 * 2
def baseEnd_4257040 : Nat := 2185907685416129545122235

theorem tailTrace_4257040 : CollatzResearch.WordTrace tailWord_4257040 prefixEnd_4257040 2185907685416129545122235 := by
  unfold tailWord_4257040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77633502248739299697068287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103511336331652399596091049 77633502248739299697068287)
  ·
    refine ⟨116450253373108949545602431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77633502248739299697068287 116450253373108949545602431)
    ·
      refine ⟨174675380059663424318403647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116450253373108949545602431 174675380059663424318403647)
      ·
        refine ⟨262013070089495136477605471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174675380059663424318403647 262013070089495136477605471)
        ·
          refine ⟨393019605134242704716408207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262013070089495136477605471 393019605134242704716408207)
          ·
            refine ⟨589529407701364057074612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393019605134242704716408207 589529407701364057074612311)
            ·
              refine ⟨884294111552046085611918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589529407701364057074612311 884294111552046085611918467)
              ·
                refine ⟨1326441167328069128417877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884294111552046085611918467 1326441167328069128417877701)
                ·
                  refine ⟨248707718874012961578352069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326441167328069128417877701 248707718874012961578352069)
                  ·
                    refine ⟨46632697288877430295941013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248707718874012961578352069 46632697288877430295941013)
                    ·
                      refine ⟨2185907685416129545122235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46632697288877430295941013 2185907685416129545122235)
                      ·
                        rfl

theorem cell23_4257040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_4257040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257040 prefixEnd_4257040 := by exact prefixLift 4257040
  have htrace : WordTrace (prefixWord ++ tailWord_4257040) baseStart_4257040 baseEnd_4257040 := by
    simpa [prefixWord, tailWord_4257040, baseEnd_4257040] using wordTrace_append hprefix tailTrace_4257040
  have hstable : (prefixWord ++ tailWord_4257040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257040).length < 2 ^ (prefixWord ++ tailWord_4257040).sum := by decide
  have hdescent : baseEnd_4257040 < baseStart_4257040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257077 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4257077 : Nat := 118140960795 + 4257077 * 2 ^ 59
def prefixEnd_4257077 : Nat := 4983230072969 + 3 ^ 40 * 4257077 * 2
def baseEnd_4257077 : Nat := 2185926684200345900359565

theorem tailTrace_4257077 : CollatzResearch.WordTrace tailWord_4257077 prefixEnd_4257077 2185926684200345900359565 := by
  unfold tailWord_4257077
  simp only [CollatzResearch.WordTrace]
  refine ⟨155268353998344554713233485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103512235998896369808822323 155268353998344554713233485)
  ·
    refine ⟨58225632749379208017462557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155268353998344554713233485 58225632749379208017462557)
    ·
      refine ⟨21834612281017203006548459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58225632749379208017462557 21834612281017203006548459)
      ·
        refine ⟨32751918421525804509822689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21834612281017203006548459 32751918421525804509822689)
        ·
          refine ⟨24563938816144353382367017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32751918421525804509822689 24563938816144353382367017)
          ·
            refine ⟨18422954112108265036775263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24563938816144353382367017 18422954112108265036775263)
            ·
              refine ⟨27634431168162397555162895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18422954112108265036775263 27634431168162397555162895)
              ·
                refine ⟨41451646752243596332744343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27634431168162397555162895 41451646752243596332744343)
                ·
                  refine ⟨62177470128365394499116515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41451646752243596332744343 62177470128365394499116515)
                  ·
                    refine ⟨93266205192548091748674773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62177470128365394499116515 93266205192548091748674773)
                    ·
                      refine ⟨2185926684200345900359565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93266205192548091748674773 2185926684200345900359565)
                      ·
                        rfl

theorem cell23_4257077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4257077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257077 prefixEnd_4257077 := by exact prefixLift 4257077
  have htrace : WordTrace (prefixWord ++ tailWord_4257077) baseStart_4257077 baseEnd_4257077 := by
    simpa [prefixWord, tailWord_4257077, baseEnd_4257077] using wordTrace_append hprefix tailTrace_4257077
  have hstable : (prefixWord ++ tailWord_4257077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257077).length < 2 ^ (prefixWord ++ tailWord_4257077).sum := by decide
  have hdescent : baseEnd_4257077 < baseStart_4257077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257104 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_4257104 : Nat := 118140960795 + 4257104 * 2 ^ 59
def prefixEnd_4257104 : Nat := 4983230072969 + 3 ^ 40 * 4257104 * 2
def baseEnd_4257104 : Nat := 2185940548178017294721941

theorem tailTrace_4257104 : CollatzResearch.WordTrace tailWord_4257104 prefixEnd_4257104 2185940548178017294721941 := by
  unfold tailWord_4257104
  simp only [CollatzResearch.WordTrace]
  refine ⟨77634669384623369162233183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103512892512831158882977577 77634669384623369162233183)
  ·
    refine ⟨116452004076935053743349775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77634669384623369162233183 116452004076935053743349775)
    ·
      refine ⟨174678006115402580615024663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116452004076935053743349775 174678006115402580615024663)
      ·
        refine ⟨262017009173103870922536995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174678006115402580615024663 262017009173103870922536995)
        ·
          refine ⟨393025513759655806383805493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262017009173103870922536995 393025513759655806383805493)
          ·
            refine ⟨36846141914967731848481765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393025513759655806383805493 36846141914967731848481765)
            ·
              refine ⟨6908651609056449721590331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36846141914967731848481765 6908651609056449721590331)
              ·
                refine ⟨10362977413584674582385497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6908651609056449721590331 10362977413584674582385497)
                ·
                  refine ⟨7772233060188505936789123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10362977413584674582385497 7772233060188505936789123)
                  ·
                    refine ⟨11658349590282758905183685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7772233060188505936789123 11658349590282758905183685)
                    ·
                      refine ⟨2185940548178017294721941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11658349590282758905183685 2185940548178017294721941)
                      ·
                        rfl

theorem cell23_4257104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_4257104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257104 prefixEnd_4257104 := by exact prefixLift 4257104
  have htrace : WordTrace (prefixWord ++ tailWord_4257104) baseStart_4257104 baseEnd_4257104 := by
    simpa [prefixWord, tailWord_4257104, baseEnd_4257104] using wordTrace_append hprefix tailTrace_4257104
  have hstable : (prefixWord ++ tailWord_4257104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257104).length < 2 ^ (prefixWord ++ tailWord_4257104).sum := by decide
  have hdescent : baseEnd_4257104 < baseStart_4257104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257214 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4257214 : Nat := 118140960795 + 4257214 * 2 ^ 59
def prefixEnd_4257214 : Nat := 4983230072969 + 3 ^ 40 * 4257214 * 2
def baseEnd_4257214 : Nat := 2185997031050011864346435

theorem tailTrace_4257214 : CollatzResearch.WordTrace tailWord_4257214 prefixEnd_4257214 2185997031050011864346435 := by
  unfold tailWord_4257214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409168849856028388871337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103515567199232151407313797 19409168849856028388871337)
  ·
    refine ⟨14556876637392021291653503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19409168849856028388871337 14556876637392021291653503)
    ·
      refine ⟨21835314956088031937480255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14556876637392021291653503 21835314956088031937480255)
      ·
        refine ⟨32752972434132047906220383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21835314956088031937480255 32752972434132047906220383)
        ·
          refine ⟨49129458651198071859330575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32752972434132047906220383 49129458651198071859330575)
          ·
            refine ⟨73694187976797107788995863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49129458651198071859330575 73694187976797107788995863)
            ·
              refine ⟨110541281965195661683493795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73694187976797107788995863 110541281965195661683493795)
              ·
                refine ⟨165811922947793492525240693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110541281965195661683493795 165811922947793492525240693)
                ·
                  refine ⟨15544867776355639924241315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165811922947793492525240693 15544867776355639924241315)
                  ·
                    refine ⟨23317301664533459886361973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15544867776355639924241315 23317301664533459886361973)
                    ·
                      refine ⟨2185997031050011864346435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23317301664533459886361973 2185997031050011864346435)
                      ·
                        rfl

theorem cell23_4257214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4257214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257214 prefixEnd_4257214 := by exact prefixLift 4257214
  have htrace : WordTrace (prefixWord ++ tailWord_4257214) baseStart_4257214 baseEnd_4257214 := by
    simpa [prefixWord, tailWord_4257214, baseEnd_4257214] using wordTrace_append hprefix tailTrace_4257214
  have hstable : (prefixWord ++ tailWord_4257214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257214).length < 2 ^ (prefixWord ++ tailWord_4257214).sum := by decide
  have hdescent : baseEnd_4257214 < baseStart_4257214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257224 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_4257224 : Nat := 118140960795 + 4257224 * 2 ^ 59
def prefixEnd_4257224 : Nat := 4983230072969 + 3 ^ 40 * 4257224 * 2
def baseEnd_4257224 : Nat := 2186002165856556825221389

theorem tailTrace_4257224 : CollatzResearch.WordTrace tailWord_4257224 prefixEnd_4257224 2186002165856556825221389 := by
  unfold tailWord_4257224
  simp only [CollatzResearch.WordTrace]
  refine ⟨77636857764405999409417363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103515810352541332545889817 77636857764405999409417363)
  ·
    refine ⟨116455286646608999114126045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77636857764405999409417363 116455286646608999114126045)
    ·
      refine ⟨43670732492478374667797267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116455286646608999114126045 43670732492478374667797267)
      ·
        refine ⟨65506098738717562001695901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43670732492478374667797267 65506098738717562001695901)
        ·
          refine ⟨24564787027019085750635963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65506098738717562001695901 24564787027019085750635963)
          ·
            refine ⟨36847180540528628625953945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24564787027019085750635963 36847180540528628625953945)
            ·
              refine ⟨27635385405396471469465459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36847180540528628625953945 27635385405396471469465459)
              ·
                refine ⟨41453078108094707204198189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27635385405396471469465459 41453078108094707204198189)
                ·
                  refine ⟨15544904290535515201574321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41453078108094707204198189 15544904290535515201574321)
                  ·
                    refine ⟨11658678217901636401180741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15544904290535515201574321 11658678217901636401180741)
                    ·
                      refine ⟨2186002165856556825221389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11658678217901636401180741 2186002165856556825221389)
                      ·
                        rfl

theorem cell23_4257224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_4257224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257224 prefixEnd_4257224 := by exact prefixLift 4257224
  have htrace : WordTrace (prefixWord ++ tailWord_4257224) baseStart_4257224 baseEnd_4257224 := by
    simpa [prefixWord, tailWord_4257224, baseEnd_4257224] using wordTrace_append hprefix tailTrace_4257224
  have hstable : (prefixWord ++ tailWord_4257224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257224).length < 2 ^ (prefixWord ++ tailWord_4257224).sum := by decide
  have hdescent : baseEnd_4257224 < baseStart_4257224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257231 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_4257231 : Nat := 118140960795 + 4257231 * 2 ^ 59
def prefixEnd_4257231 : Nat := 4983230072969 + 3 ^ 40 * 4257231 * 2
def baseEnd_4257231 : Nat := 2186005760221138297833857

theorem tailTrace_4257231 : CollatzResearch.WordTrace tailWord_4257231 prefixEnd_4257231 2186005760221138297833857 := by
  unfold tailWord_4257231
  simp only [CollatzResearch.WordTrace]
  refine ⟨155273970839786639014339547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103515980559857759342893031 155273970839786639014339547)
  ·
    refine ⟨232910956259679958521509321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155273970839786639014339547 232910956259679958521509321)
    ·
      refine ⟨174683217194759968891131991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232910956259679958521509321 174683217194759968891131991)
      ·
        refine ⟨262024825792139953336697987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174683217194759968891131991 262024825792139953336697987)
        ·
          refine ⟨393037238688209930005046981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262024825792139953336697987 393037238688209930005046981)
          ·
            refine ⟨73694482254039361875946309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393037238688209930005046981 73694482254039361875946309)
            ·
              refine ⟨13817715422632380351739933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73694482254039361875946309 13817715422632380351739933)
              ·
                refine ⟨5181643283487142631902475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13817715422632380351739933 5181643283487142631902475)
                ·
                  refine ⟨7772464925230713947853713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181643283487142631902475 7772464925230713947853713)
                  ·
                    refine ⟨5829348693923035460890285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7772464925230713947853713 5829348693923035460890285)
                    ·
                      refine ⟨2186005760221138297833857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5829348693923035460890285 2186005760221138297833857)
                      ·
                        rfl

theorem cell23_4257231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_4257231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257231 prefixEnd_4257231 := by exact prefixLift 4257231
  have htrace : WordTrace (prefixWord ++ tailWord_4257231) baseStart_4257231 baseEnd_4257231 := by
    simpa [prefixWord, tailWord_4257231, baseEnd_4257231] using wordTrace_append hprefix tailTrace_4257231
  have hstable : (prefixWord ++ tailWord_4257231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257231).length < 2 ^ (prefixWord ++ tailWord_4257231).sum := by decide
  have hdescent : baseEnd_4257231 < baseStart_4257231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257238 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4257238 : Nat := 118140960795 + 4257238 * 2 ^ 59
def prefixEnd_4257238 : Nat := 4983230072969 + 3 ^ 40 * 4257238 * 2
def baseEnd_4257238 : Nat := 728669784861906590148775

theorem tailTrace_4257238 : CollatzResearch.WordTrace tailWord_4257238 prefixEnd_4257238 728669784861906590148775 := by
  unfold tailWord_4257238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704639134422579950615273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103516150767174186139896245 9704639134422579950615273)
  ·
    refine ⟨7278479350816934962961455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9704639134422579950615273 7278479350816934962961455)
    ·
      refine ⟨10917719026225402444442183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278479350816934962961455 10917719026225402444442183)
      ·
        refine ⟨16376578539338103666663275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10917719026225402444442183 16376578539338103666663275)
        ·
          refine ⟨24564867809007155499994913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16376578539338103666663275 24564867809007155499994913)
          ·
            refine ⟨18423650856755366624996185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24564867809007155499994913 18423650856755366624996185)
            ·
              refine ⟨13817738142566524968747139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18423650856755366624996185 13817738142566524968747139)
              ·
                refine ⟨20726607213849787453120709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13817738142566524968747139 20726607213849787453120709)
                ·
                  refine ⟨3886238852596835147460133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20726607213849787453120709 3886238852596835147460133)
                  ·
                    refine ⟨728669784861906590148775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886238852596835147460133 728669784861906590148775)
                    ·
                      rfl

theorem cell23_4257238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4257238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257238 prefixEnd_4257238 := by exact prefixLift 4257238
  have htrace : WordTrace (prefixWord ++ tailWord_4257238) baseStart_4257238 baseEnd_4257238 := by
    simpa [prefixWord, tailWord_4257238, baseEnd_4257238] using wordTrace_append hprefix tailTrace_4257238
  have hstable : (prefixWord ++ tailWord_4257238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257238).length < 2 ^ (prefixWord ++ tailWord_4257238).sum := by decide
  have hdescent : baseEnd_4257238 < baseStart_4257238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257245 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_4257245 : Nat := 118140960795 + 4257245 * 2 ^ 59
def prefixEnd_4257245 : Nat := 4983230072969 + 3 ^ 40 * 4257245 * 2
def baseEnd_4257245 : Nat := 2186012948950301243058793

theorem tailTrace_4257245 : CollatzResearch.WordTrace tailWord_4257245 prefixEnd_4257245 2186012948950301243058793 := by
  unfold tailWord_4257245
  simp only [CollatzResearch.WordTrace]
  refine ⟨155274481461735919405349189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103516320974490612936899459 155274481461735919405349189)
  ·
    refine ⟨29113965274075484888502973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155274481461735919405349189 29113965274075484888502973)
    ·
      refine ⟨10917736977778306833188615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29113965274075484888502973 10917736977778306833188615)
      ·
        refine ⟨16376605466667460249782923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10917736977778306833188615 16376605466667460249782923)
        ·
          refine ⟨24564908200001190374674385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16376605466667460249782923 24564908200001190374674385)
          ·
            refine ⟨18423681150000892781005789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24564908200001190374674385 18423681150000892781005789)
            ·
              refine ⟨6908880431250334792877171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18423681150000892781005789 6908880431250334792877171)
              ·
                refine ⟨10363320646875502189315757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6908880431250334792877171 10363320646875502189315757)
                ·
                  refine ⟨3886245242578313320993409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10363320646875502189315757 3886245242578313320993409)
                  ·
                    refine ⟨2914683931933734990745057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886245242578313320993409 2914683931933734990745057)
                    ·
                      refine ⟨2186012948950301243058793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914683931933734990745057 2186012948950301243058793)
                      ·
                        rfl

theorem cell23_4257245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_4257245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257245 prefixEnd_4257245 := by exact prefixLift 4257245
  have htrace : WordTrace (prefixWord ++ tailWord_4257245) baseStart_4257245 baseEnd_4257245 := by
    simpa [prefixWord, tailWord_4257245, baseEnd_4257245] using wordTrace_append hprefix tailTrace_4257245
  have hstable : (prefixWord ++ tailWord_4257245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257245).length < 2 ^ (prefixWord ++ tailWord_4257245).sum := by decide
  have hdescent : baseEnd_4257245 < baseStart_4257245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257255 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 2, 4]
def baseStart_4257255 : Nat := 118140960795 + 4257255 * 2 ^ 59
def prefixEnd_4257255 : Nat := 4983230072969 + 3 ^ 40 * 4257255 * 2
def baseEnd_4257255 : Nat := 728672694585615401311249

theorem tailTrace_4257255 : CollatzResearch.WordTrace tailWord_4257255 prefixEnd_4257255 728672694585615401311249 := by
  unfold tailWord_4257255
  simp only [CollatzResearch.WordTrace]
  refine ⟨155274846191699691113213219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103516564127799794075475479 155274846191699691113213219)
  ·
    refine ⟨232912269287549536669819829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155274846191699691113213219 232912269287549536669819829)
    ·
      refine ⟨21835525245707769062795609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232912269287549536669819829 21835525245707769062795609)
      ·
        refine ⟨16376643934280826797096707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21835525245707769062795609 16376643934280826797096707)
        ·
          refine ⟨24564965901421240195645061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16376643934280826797096707 24564965901421240195645061)
          ·
            refine ⟨4605931106516482536683449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24564965901421240195645061 4605931106516482536683449)
            ·
              refine ⟨3454448329887361902512587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605931106516482536683449 3454448329887361902512587)
              ·
                refine ⟨5181672494831042853768881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454448329887361902512587 5181672494831042853768881)
                ·
                  refine ⟨3886254371123282140326661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5181672494831042853768881 3886254371123282140326661)
                  ·
                    refine ⟨728672694585615401311249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886254371123282140326661 728672694585615401311249)
                    ·
                      rfl

theorem cell23_4257255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_4257255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257255 prefixEnd_4257255 := by exact prefixLift 4257255
  have htrace : WordTrace (prefixWord ++ tailWord_4257255) baseStart_4257255 baseEnd_4257255 := by
    simpa [prefixWord, tailWord_4257255, baseEnd_4257255] using wordTrace_append hprefix tailTrace_4257255
  have hstable : (prefixWord ++ tailWord_4257255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257255).length < 2 ^ (prefixWord ++ tailWord_4257255).sum := by decide
  have hdescent : baseEnd_4257255 < baseStart_4257255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257282 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4257282 : Nat := 118140960795 + 4257282 * 2 ^ 59
def prefixEnd_4257282 : Nat := 4983230072969 + 3 ^ 40 * 4257282 * 2
def baseEnd_4257282 : Nat := 2186031947734517598296123

theorem tailTrace_4257282 : CollatzResearch.WordTrace tailWord_4257282 prefixEnd_4257282 2186031947734517598296123 := by
  unfold tailWord_4257282
  simp only [CollatzResearch.WordTrace]
  refine ⟨38818957740650468681111525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103517220641734583149630733 38818957740650468681111525)
  ·
    refine ⟨7278554576371962877708411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38818957740650468681111525 7278554576371962877708411)
    ·
      refine ⟨10917831864557944316562617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278554576371962877708411 10917831864557944316562617)
      ·
        refine ⟨8188373898418458237421963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10917831864557944316562617 8188373898418458237421963)
        ·
          refine ⟨12282560847627687356132945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188373898418458237421963 12282560847627687356132945)
          ·
            refine ⟨9211920635720765517099709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12282560847627687356132945 9211920635720765517099709)
            ·
              refine ⟨3454470238395287068912391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9211920635720765517099709 3454470238395287068912391)
              ·
                refine ⟨5181705357592930603368587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454470238395287068912391 5181705357592930603368587)
                ·
                  refine ⟨7772558036389395905052881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181705357592930603368587 7772558036389395905052881)
                  ·
                    refine ⟨5829418527292046928789661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7772558036389395905052881 5829418527292046928789661)
                    ·
                      refine ⟨2186031947734517598296123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5829418527292046928789661 2186031947734517598296123)
                      ·
                        rfl

theorem cell23_4257282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4257282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257282 prefixEnd_4257282 := by exact prefixLift 4257282
  have htrace : WordTrace (prefixWord ++ tailWord_4257282) baseStart_4257282 baseEnd_4257282 := by
    simpa [prefixWord, tailWord_4257282, baseEnd_4257282] using wordTrace_append hprefix tailTrace_4257282
  have hstable : (prefixWord ++ tailWord_4257282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257282).length < 2 ^ (prefixWord ++ tailWord_4257282).sum := by decide
  have hdescent : baseEnd_4257282 < baseStart_4257282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257288 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_4257288 : Nat := 118140960795 + 4257288 * 2 ^ 59
def prefixEnd_4257288 : Nat := 4983230072969 + 3 ^ 40 * 4257288 * 2
def baseEnd_4257288 : Nat := 2186035028618444574821095

theorem tailTrace_4257288 : CollatzResearch.WordTrace tailWord_4257288 prefixEnd_4257288 2186035028618444574821095 := by
  unfold tailWord_4257288
  simp only [CollatzResearch.WordTrace]
  refine ⟨77638024900290068874582259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103517366533720091832776345 77638024900290068874582259)
  ·
    refine ⟨116457037350435103311873389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77638024900290068874582259 116457037350435103311873389)
    ·
      refine ⟨43671389006413163741952521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116457037350435103311873389 43671389006413163741952521)
      ·
        refine ⟨32753541754809872806464391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43671389006413163741952521 32753541754809872806464391)
        ·
          refine ⟨49130312632214809209696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32753541754809872806464391 49130312632214809209696587)
          ·
            refine ⟨73695468948322213814544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49130312632214809209696587 73695468948322213814544881)
            ·
              refine ⟨55271601711241660360908661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73695468948322213814544881 55271601711241660360908661)
              ·
                refine ⟨5181712660428905658835187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55271601711241660360908661 5181712660428905658835187)
                ·
                  refine ⟨7772568990643358488252781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181712660428905658835187 7772568990643358488252781)
                  ·
                    refine ⟨2914713371491259433094793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7772568990643358488252781 2914713371491259433094793)
                    ·
                      refine ⟨2186035028618444574821095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914713371491259433094793 2186035028618444574821095)
                      ·
                        rfl

theorem cell23_4257288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_4257288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257288 prefixEnd_4257288 := by exact prefixLift 4257288
  have htrace : WordTrace (prefixWord ++ tailWord_4257288) baseStart_4257288 baseEnd_4257288 := by
    simpa [prefixWord, tailWord_4257288, baseEnd_4257288] using wordTrace_append hprefix tailTrace_4257288
  have hstable : (prefixWord ++ tailWord_4257288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257288).length < 2 ^ (prefixWord ++ tailWord_4257288).sum := by decide
  have hdescent : baseEnd_4257288 < baseStart_4257288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257391 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_4257391 : Nat := 118140960795 + 4257391 * 2 ^ 59
def prefixEnd_4257391 : Nat := 4983230072969 + 3 ^ 40 * 4257391 * 2
def baseEnd_4257391 : Nat := 2186087917125857671833121

theorem tailTrace_4257391 : CollatzResearch.WordTrace tailWord_4257391 prefixEnd_4257391 2186087917125857671833121 := by
  unfold tailWord_4257391
  simp only [CollatzResearch.WordTrace]
  refine ⟨155279806519206986340164027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103519871012804657560109351 155279806519206986340164027)
  ·
    refine ⟨232919709778810479510246041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155279806519206986340164027 232919709778810479510246041)
    ·
      refine ⟨174689782334107859632684531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232919709778810479510246041 174689782334107859632684531)
      ·
        refine ⟨262034673501161789449026797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174689782334107859632684531 262034673501161789449026797)
        ·
          refine ⟨98263002562935671043385049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262034673501161789449026797 98263002562935671043385049)
          ·
            refine ⟨73697251922201753282538787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98263002562935671043385049 73697251922201753282538787)
            ·
              refine ⟨110545877883302629923808181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73697251922201753282538787 110545877883302629923808181)
              ·
                refine ⟨10363676051559621555357017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110545877883302629923808181 10363676051559621555357017)
                ·
                  refine ⟨7772757038669716166517763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10363676051559621555357017 7772757038669716166517763)
                  ·
                    refine ⟨11659135558004574249776645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7772757038669716166517763 11659135558004574249776645)
                    ·
                      refine ⟨2186087917125857671833121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11659135558004574249776645 2186087917125857671833121)
                      ·
                        rfl

theorem cell23_4257391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_4257391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257391 prefixEnd_4257391 := by exact prefixLift 4257391
  have htrace : WordTrace (prefixWord ++ tailWord_4257391) baseStart_4257391 baseEnd_4257391 := by
    simpa [prefixWord, tailWord_4257391, baseEnd_4257391] using wordTrace_append hprefix tailTrace_4257391
  have hstable : (prefixWord ++ tailWord_4257391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257391).length < 2 ^ (prefixWord ++ tailWord_4257391).sum := by decide
  have hdescent : baseEnd_4257391 < baseStart_4257391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257442 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4257442 : Nat := 118140960795 + 4257442 * 2 ^ 59
def prefixEnd_4257442 : Nat := 4983230072969 + 3 ^ 40 * 4257442 * 2
def baseEnd_4257442 : Nat := 2186114104639236972295387

theorem tailTrace_4257442 : CollatzResearch.WordTrace tailWord_4257442 prefixEnd_4257442 2186114104639236972295387 := by
  unfold tailWord_4257442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38820416660505555512567645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103521111094681481366847053 38820416660505555512567645)
  ·
    refine ⟨14557656247689583317212867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38820416660505555512567645 14557656247689583317212867)
    ·
      refine ⟨21836484371534374975819301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14557656247689583317212867 21836484371534374975819301)
      ·
        refine ⟨4094340819662695307966119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21836484371534374975819301 4094340819662695307966119)
        ·
          refine ⟨6141511229494042961949179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4094340819662695307966119 6141511229494042961949179)
          ·
            refine ⟨9212266844241064442923769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6141511229494042961949179 9212266844241064442923769)
            ·
              refine ⟨6909200133180798332192827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9212266844241064442923769 6909200133180798332192827)
              ·
                refine ⟨10363800199771197498289241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6909200133180798332192827 10363800199771197498289241)
                ·
                  refine ⟨7772850149828398123716931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10363800199771197498289241 7772850149828398123716931)
                  ·
                    refine ⟨11659275224742597185575397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7772850149828398123716931 11659275224742597185575397)
                    ·
                      refine ⟨2186114104639236972295387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11659275224742597185575397 2186114104639236972295387)
                      ·
                        rfl

theorem cell23_4257442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4257442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257442 prefixEnd_4257442 := by exact prefixLift 4257442
  have htrace : WordTrace (prefixWord ++ tailWord_4257442) baseStart_4257442 baseEnd_4257442 := by
    simpa [prefixWord, tailWord_4257442, baseEnd_4257442] using wordTrace_append hprefix tailTrace_4257442
  have hstable : (prefixWord ++ tailWord_4257442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257442).length < 2 ^ (prefixWord ++ tailWord_4257442).sum := by decide
  have hdescent : baseEnd_4257442 < baseStart_4257442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
