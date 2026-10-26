import V185TrunkScan23Chunk1232

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7305657 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7305657 : Nat := 118140960795 + 7305657 * 2 ^ 59
def prefixEnd_7305657 : Nat := 4983230072969 + 3 ^ 40 * 7305657 * 2
def baseEnd_7305657 : Nat := 3751313537884028317089401

theorem tailTrace_7305657 : CollatzResearch.WordTrace tailWord_7305657 prefixEnd_7305657 3751313537884028317089401 := by
  unfold tailWord_7305657
  simp only [CollatzResearch.WordTrace]
  refine ⟨266459201293859870725691225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177639467529239913817127483 266459201293859870725691225)
  ·
    refine ⟨199844400970394903044268419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266459201293859870725691225 199844400970394903044268419)
    ·
      refine ⟨299766601455592354566402629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199844400970394903044268419 299766601455592354566402629)
      ·
        refine ⟨56206237772923566481200493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299766601455592354566402629 56206237772923566481200493)
        ·
          refine ⟨21077339164846337430450185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56206237772923566481200493 21077339164846337430450185)
          ·
            refine ⟨15808004373634753072837639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21077339164846337430450185 15808004373634753072837639)
            ·
              refine ⟨23712006560452129609256459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808004373634753072837639 23712006560452129609256459)
              ·
                refine ⟨35568009840678194413884689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23712006560452129609256459 35568009840678194413884689)
                ·
                  refine ⟨26676007380508645810413517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35568009840678194413884689 26676007380508645810413517)
                  ·
                    refine ⟨10003502767690742178905069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26676007380508645810413517 10003502767690742178905069)
                    ·
                      refine ⟨3751313537884028317089401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003502767690742178905069 3751313537884028317089401)
                      ·
                        rfl

theorem cell23_7305657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7305657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305657 prefixEnd_7305657 := by exact prefixLift 7305657
  have htrace : WordTrace (prefixWord ++ tailWord_7305657) baseStart_7305657 baseEnd_7305657 := by
    simpa [prefixWord, tailWord_7305657, baseEnd_7305657] using wordTrace_append hprefix tailTrace_7305657
  have hstable : (prefixWord ++ tailWord_7305657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305657).length < 2 ^ (prefixWord ++ tailWord_7305657).sum := by decide
  have hdescent : baseEnd_7305657 < baseStart_7305657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305697 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_7305697 : Nat := 118140960795 + 7305697 * 2 ^ 59
def prefixEnd_7305697 : Nat := 4983230072969 + 3 ^ 40 * 7305697 * 2
def baseEnd_7305697 : Nat := 3751334077110208160589217

theorem tailTrace_7305697 : CollatzResearch.WordTrace tailWord_7305697 prefixEnd_7305697 3751334077110208160589217 := by
  unfold tailWord_7305697
  simp only [CollatzResearch.WordTrace]
  refine ⟨266460660213714957557147345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177640440142476638371431563 266460660213714957557147345)
  ·
    refine ⟨199845495160286218167860509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266460660213714957557147345 199845495160286218167860509)
    ·
      refine ⟨74942060685107331812947691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199845495160286218167860509 74942060685107331812947691)
      ·
        refine ⟨112413091027660997719421537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74942060685107331812947691 112413091027660997719421537)
        ·
          refine ⟨84309818270745748289566153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112413091027660997719421537 84309818270745748289566153)
          ·
            refine ⟨63232363703059311217174615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84309818270745748289566153 63232363703059311217174615)
            ·
              refine ⟨94848545554588966825761923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63232363703059311217174615 94848545554588966825761923)
              ·
                refine ⟨142272818331883450238642885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94848545554588966825761923 142272818331883450238642885)
                ·
                  refine ⟨26676153437228146919745541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142272818331883450238642885 26676153437228146919745541)
                  ·
                    refine ⟨5001778769480277547452289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26676153437228146919745541 5001778769480277547452289)
                    ·
                      refine ⟨3751334077110208160589217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001778769480277547452289 3751334077110208160589217)
                      ·
                        rfl

theorem cell23_7305697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_7305697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305697 prefixEnd_7305697 := by exact prefixLift 7305697
  have htrace : WordTrace (prefixWord ++ tailWord_7305697) baseStart_7305697 baseEnd_7305697 := by
    simpa [prefixWord, tailWord_7305697, baseEnd_7305697] using wordTrace_append hprefix tailTrace_7305697
  have hstable : (prefixWord ++ tailWord_7305697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305697).length < 2 ^ (prefixWord ++ tailWord_7305697).sum := by decide
  have hdescent : baseEnd_7305697 < baseStart_7305697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305707 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 3, 4]
def baseStart_7305707 : Nat := 118140960795 + 7305707 * 2 ^ 59
def prefixEnd_7305707 : Nat := 4983230072969 + 3 ^ 40 * 7305707 * 2
def baseEnd_7305707 : Nat := 1250446403972251040488057

theorem tailTrace_7305707 : CollatzResearch.WordTrace tailWord_7305707 prefixEnd_7305707 1250446403972251040488057 := by
  unfold tailWord_7305707
  simp only [CollatzResearch.WordTrace]
  refine ⟨266461024943678729265011375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177640683295785819510007583 266461024943678729265011375)
  ·
    refine ⟨399691537415518093897517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266461024943678729265011375 399691537415518093897517063)
    ·
      refine ⟨599537306123277140846275595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399691537415518093897517063 599537306123277140846275595)
      ·
        refine ⟨899305959184915711269413393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599537306123277140846275595 899305959184915711269413393)
        ·
          refine ⟨674479469388686783452060045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899305959184915711269413393 674479469388686783452060045)
          ·
            refine ⟨252929801020757543794522517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674479469388686783452060045 252929801020757543794522517)
            ·
              refine ⟨11856084422848009865368243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252929801020757543794522517 11856084422848009865368243)
              ·
                refine ⟨17784126634272014798052365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856084422848009865368243 17784126634272014798052365)
                ·
                  refine ⟨6669047487852005549269637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17784126634272014798052365 6669047487852005549269637)
                  ·
                    refine ⟨1250446403972251040488057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669047487852005549269637 1250446403972251040488057)
                    ·
                      rfl

theorem cell23_7305707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 4].length) (baseStart_7305707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305707 prefixEnd_7305707 := by exact prefixLift 7305707
  have htrace : WordTrace (prefixWord ++ tailWord_7305707) baseStart_7305707 baseEnd_7305707 := by
    simpa [prefixWord, tailWord_7305707, baseEnd_7305707] using wordTrace_append hprefix tailTrace_7305707
  have hstable : (prefixWord ++ tailWord_7305707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305707).length < 2 ^ (prefixWord ++ tailWord_7305707).sum := by decide
  have hdescent : baseEnd_7305707 < baseStart_7305707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305751 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7305751 : Nat := 118140960795 + 7305751 * 2 ^ 59
def prefixEnd_7305751 : Nat := 4983230072969 + 3 ^ 40 * 7305751 * 2
def baseEnd_7305751 : Nat := 3751361805065550949313969

theorem tailTrace_7305751 : CollatzResearch.WordTrace tailWord_7305751 prefixEnd_7305751 3751361805065550949313969 := by
  unfold tailWord_7305751
  simp only [CollatzResearch.WordTrace]
  refine ⟨266462629755519324779613107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177641753170346216519742071 266462629755519324779613107)
  ·
    refine ⟨399693944633278987169419661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266462629755519324779613107 399693944633278987169419661)
    ·
      refine ⟨149885229237479620188532373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399693944633278987169419661 149885229237479620188532373)
      ·
        refine ⟨7025870120506857196337455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149885229237479620188532373 7025870120506857196337455)
        ·
          refine ⟨10538805180760285794506183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025870120506857196337455 10538805180760285794506183)
          ·
            refine ⟨15808207771140428691759275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538805180760285794506183 15808207771140428691759275)
            ·
              refine ⟨23712311656710643037638913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808207771140428691759275 23712311656710643037638913)
              ·
                refine ⟨17784233742532982278229185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23712311656710643037638913 17784233742532982278229185)
                ·
                  refine ⟨13338175306899736708671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17784233742532982278229185 13338175306899736708671889)
                  ·
                    refine ⟨10003631480174802531503917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13338175306899736708671889 10003631480174802531503917)
                    ·
                      refine ⟨3751361805065550949313969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003631480174802531503917 3751361805065550949313969)
                      ·
                        rfl

theorem cell23_7305751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7305751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305751 prefixEnd_7305751 := by exact prefixLift 7305751
  have htrace : WordTrace (prefixWord ++ tailWord_7305751) baseStart_7305751 baseEnd_7305751 := by
    simpa [prefixWord, tailWord_7305751, baseEnd_7305751] using wordTrace_append hprefix tailTrace_7305751
  have hstable : (prefixWord ++ tailWord_7305751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305751).length < 2 ^ (prefixWord ++ tailWord_7305751).sum := by decide
  have hdescent : baseEnd_7305751 < baseStart_7305751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305797 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_7305797 : Nat := 118140960795 + 7305797 * 2 ^ 59
def prefixEnd_7305797 : Nat := 4983230072969 + 3 ^ 40 * 7305797 * 2
def baseEnd_7305797 : Nat := 1250461808391885923112919

theorem tailTrace_7305797 : CollatzResearch.WordTrace tailWord_7305797 prefixEnd_7305797 1250461808391885923112919 := by
  unfold tailWord_7305797
  simp only [CollatzResearch.WordTrace]
  refine ⟨266464307513352674635787645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177642871675568449757191763 266464307513352674635787645)
  ·
    refine ⟨99924115317507252988420367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266464307513352674635787645 99924115317507252988420367)
    ·
      refine ⟨149886172976260879482630551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99924115317507252988420367 149886172976260879482630551)
      ·
        refine ⟨224829259464391319223945827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149886172976260879482630551 224829259464391319223945827)
        ·
          refine ⟨337243889196586978835918741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224829259464391319223945827 337243889196586978835918741)
          ·
            refine ⟨15808307306090014632933691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337243889196586978835918741 15808307306090014632933691)
            ·
              refine ⟨23712460959135021949400537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808307306090014632933691 23712460959135021949400537)
              ·
                refine ⟨17784345719351266462050403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23712460959135021949400537 17784345719351266462050403)
                ·
                  refine ⟨26676518579026899693075605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784345719351266462050403 26676518579026899693075605)
                  ·
                    refine ⟨1250461808391885923112919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26676518579026899693075605 1250461808391885923112919)
                    ·
                      rfl

theorem cell23_7305797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_7305797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305797 prefixEnd_7305797 := by exact prefixLift 7305797
  have htrace : WordTrace (prefixWord ++ tailWord_7305797) baseStart_7305797 baseEnd_7305797 := by
    simpa [prefixWord, tailWord_7305797, baseEnd_7305797] using wordTrace_append hprefix tailTrace_7305797
  have hstable : (prefixWord ++ tailWord_7305797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305797).length < 2 ^ (prefixWord ++ tailWord_7305797).sum := by decide
  have hdescent : baseEnd_7305797 < baseStart_7305797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305807 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_7305807 : Nat := 118140960795 + 7305807 * 2 ^ 59
def prefixEnd_7305807 : Nat := 4983230072969 + 3 ^ 40 * 7305807 * 2
def baseEnd_7305807 : Nat := 3751390559982202730213711

theorem tailTrace_7305807 : CollatzResearch.WordTrace tailWord_7305807 prefixEnd_7305807 3751390559982202730213711 := by
  unfold tailWord_7305807
  simp only [CollatzResearch.WordTrace]
  refine ⟨266464672243316446343651675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177643114828877630895767783 266464672243316446343651675)
  ·
    refine ⟨399697008364974669515477513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266464672243316446343651675 399697008364974669515477513)
    ·
      refine ⟨299772756273731002136608135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399697008364974669515477513 299772756273731002136608135)
      ·
        refine ⟨449659134410596503204912203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299772756273731002136608135 449659134410596503204912203)
        ·
          refine ⟨674488701615894754807368305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449659134410596503204912203 674488701615894754807368305)
          ·
            refine ⟨505866526211921066105526229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674488701615894754807368305 505866526211921066105526229)
            ·
              refine ⟨11856246708091899986848271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 505866526211921066105526229 11856246708091899986848271)
              ·
                refine ⟨17784370062137849980272407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856246708091899986848271 17784370062137849980272407)
                ·
                  refine ⟨26676555093206774970408611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784370062137849980272407 26676555093206774970408611)
                  ·
                    refine ⟨40014832639810162455612917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26676555093206774970408611 40014832639810162455612917)
                    ·
                      refine ⟨3751390559982202730213711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40014832639810162455612917 3751390559982202730213711)
                      ·
                        rfl

theorem cell23_7305807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_7305807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305807 prefixEnd_7305807 := by exact prefixLift 7305807
  have htrace : WordTrace (prefixWord ++ tailWord_7305807) baseStart_7305807 baseEnd_7305807 := by
    simpa [prefixWord, tailWord_7305807, baseEnd_7305807] using wordTrace_append hprefix tailTrace_7305807
  have hstable : (prefixWord ++ tailWord_7305807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305807).length < 2 ^ (prefixWord ++ tailWord_7305807).sum := by decide
  have hdescent : baseEnd_7305807 < baseStart_7305807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305834 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7305834 : Nat := 118140960795 + 7305834 * 2 ^ 59
def prefixEnd_7305834 : Nat := 4983230072969 + 3 ^ 40 * 7305834 * 2
def baseEnd_7305834 : Nat := 3751404423959874124576087

theorem tailTrace_7305834 : CollatzResearch.WordTrace tailWord_7305834 prefixEnd_7305834 3751404423959874124576087 := by
  unfold tailWord_7305834
  simp only [CollatzResearch.WordTrace]
  refine ⟨66616414253554657488721139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177643771342812419969923037 66616414253554657488721139)
  ·
    refine ⟨99924621380331986233081709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66616414253554657488721139 99924621380331986233081709)
    ·
      refine ⟨37471733017624494837405641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99924621380331986233081709 37471733017624494837405641)
      ·
        refine ⟨28103799763218371128054231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37471733017624494837405641 28103799763218371128054231)
        ·
          refine ⟨42155699644827556692081347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28103799763218371128054231 42155699644827556692081347)
          ·
            refine ⟨63233549467241335038122021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42155699644827556692081347 63233549467241335038122021)
            ·
              refine ⟨11856290525107750319647879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63233549467241335038122021 11856290525107750319647879)
              ·
                refine ⟨17784435787661625479471819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856290525107750319647879 17784435787661625479471819)
                ·
                  refine ⟨26676653681492438219207729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784435787661625479471819 26676653681492438219207729)
                  ·
                    refine ⟨20007490261119328664405797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26676653681492438219207729 20007490261119328664405797)
                    ·
                      refine ⟨3751404423959874124576087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20007490261119328664405797 3751404423959874124576087)
                      ·
                        rfl

theorem cell23_7305834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7305834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305834 prefixEnd_7305834 := by exact prefixLift 7305834
  have htrace : WordTrace (prefixWord ++ tailWord_7305834) baseStart_7305834 baseEnd_7305834 := by
    simpa [prefixWord, tailWord_7305834, baseEnd_7305834] using wordTrace_append hprefix tailTrace_7305834
  have hstable : (prefixWord ++ tailWord_7305834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305834).length < 2 ^ (prefixWord ++ tailWord_7305834).sum := by decide
  have hdescent : baseEnd_7305834 < baseStart_7305834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305838 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_7305838 : Nat := 118140960795 + 7305838 * 2 ^ 59
def prefixEnd_7305838 : Nat := 4983230072969 + 3 ^ 40 * 7305838 * 2
def baseEnd_7305838 : Nat := 3751406477882492108926069

theorem tailTrace_7305838 : CollatzResearch.WordTrace tailWord_7305838 prefixEnd_7305838 3751406477882492108926069 := by
  unfold tailWord_7305838
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308225363275517329753771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177643868604136092425353445 33308225363275517329753771)
  ·
    refine ⟨49962338044913275994630657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33308225363275517329753771 49962338044913275994630657)
    ·
      refine ⟨37471753533684956995972993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49962338044913275994630657 37471753533684956995972993)
      ·
        refine ⟨28103815150263717746979745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37471753533684956995972993 28103815150263717746979745)
        ·
          refine ⟨21077861362697788310234809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28103815150263717746979745 21077861362697788310234809)
          ·
            refine ⟨15808396022023341232676107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21077861362697788310234809 15808396022023341232676107)
            ·
              refine ⟨23712594033035011849014161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808396022023341232676107 23712594033035011849014161)
              ·
                refine ⟨17784445524776258886760621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23712594033035011849014161 17784445524776258886760621)
                ·
                  refine ⟨6669167071791097082535233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17784445524776258886760621 6669167071791097082535233)
                  ·
                    refine ⟨5001875303843322811901425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6669167071791097082535233 5001875303843322811901425)
                    ·
                      refine ⟨3751406477882492108926069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001875303843322811901425 3751406477882492108926069)
                      ·
                        rfl

theorem cell23_7305838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_7305838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305838 prefixEnd_7305838 := by exact prefixLift 7305838
  have htrace : WordTrace (prefixWord ++ tailWord_7305838) baseStart_7305838 baseEnd_7305838 := by
    simpa [prefixWord, tailWord_7305838, baseEnd_7305838] using wordTrace_append hprefix tailTrace_7305838
  have hstable : (prefixWord ++ tailWord_7305838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305838).length < 2 ^ (prefixWord ++ tailWord_7305838).sum := by decide
  have hdescent : baseEnd_7305838 < baseStart_7305838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305888 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3]
def baseStart_7305888 : Nat := 118140960795 + 7305888 * 2 ^ 59
def prefixEnd_7305888 : Nat := 4983230072969 + 3 ^ 40 * 7305888 * 2
def baseEnd_7305888 : Nat := 3751432151915216913300839

theorem tailTrace_7305888 : CollatzResearch.WordTrace tailWord_7305888 prefixEnd_7305888 3751432151915216913300839 := by
  unfold tailWord_7305888
  simp only [CollatzResearch.WordTrace]
  refine ⟨133233813278011498588675159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177645084370681998118233545 133233813278011498588675159)
  ·
    refine ⟨199850719917017247883012739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133233813278011498588675159 199850719917017247883012739)
    ·
      refine ⟨299776079875525871824519109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199850719917017247883012739 299776079875525871824519109)
      ·
        refine ⟨56208014976661100967097333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299776079875525871824519109 56208014976661100967097333)
        ·
          refine ⟨5269501404061978215665375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56208014976661100967097333 5269501404061978215665375)
          ·
            refine ⟨7904252106092967323498063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269501404061978215665375 7904252106092967323498063)
            ·
              refine ⟨11856378159139450985247095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904252106092967323498063 11856378159139450985247095)
              ·
                refine ⟨17784567238709176477870643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856378159139450985247095 17784567238709176477870643)
                ·
                  refine ⟨26676850858063764716805965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784567238709176477870643 26676850858063764716805965)
                  ·
                    refine ⟨10003819071773911768802237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26676850858063764716805965 10003819071773911768802237)
                    ·
                      refine ⟨3751432151915216913300839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003819071773911768802237 3751432151915216913300839)
                      ·
                        rfl

theorem cell23_7305888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_7305888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305888 prefixEnd_7305888 := by exact prefixLift 7305888
  have htrace : WordTrace (prefixWord ++ tailWord_7305888) baseStart_7305888 baseEnd_7305888 := by
    simpa [prefixWord, tailWord_7305888, baseEnd_7305888] using wordTrace_append hprefix tailTrace_7305888
  have hstable : (prefixWord ++ tailWord_7305888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305888).length < 2 ^ (prefixWord ++ tailWord_7305888).sum := by decide
  have hdescent : baseEnd_7305888 < baseStart_7305888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305897 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_7305897 : Nat := 118140960795 + 7305897 * 2 ^ 59
def prefixEnd_7305897 : Nat := 4983230072969 + 3 ^ 40 * 7305897 * 2
def baseEnd_7305897 : Nat := 3751436773241107378088297

theorem tailTrace_7305897 : CollatzResearch.WordTrace tailWord_7305897 prefixEnd_7305897 3751436773241107378088297 := by
  unfold tailWord_7305897
  simp only [CollatzResearch.WordTrace]
  refine ⟨266467954812990391714427945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177645303208660261142951963 266467954812990391714427945)
  ·
    refine ⟨199850966109742793785820959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266467954812990391714427945 199850966109742793785820959)
    ·
      refine ⟨299776449164614190678731439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199850966109742793785820959 299776449164614190678731439)
      ·
        refine ⟨449664673746921286018097159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299776449164614190678731439 449664673746921286018097159)
        ·
          refine ⟨674497010620381929027145739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449664673746921286018097159 674497010620381929027145739)
          ·
            refine ⟨1011745515930572893540718609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674497010620381929027145739 1011745515930572893540718609)
            ·
              refine ⟨758809136947929670155538957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011745515930572893540718609 758809136947929670155538957)
              ·
                refine ⟨284553426355473626308327109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758809136947929670155538957 284553426355473626308327109)
                ·
                  refine ⟨53353767441651304932811333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284553426355473626308327109 53353767441651304932811333)
                  ·
                    refine ⟨10003831395309619674902125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53353767441651304932811333 10003831395309619674902125)
                    ·
                      refine ⟨3751436773241107378088297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003831395309619674902125 3751436773241107378088297)
                      ·
                        rfl

theorem cell23_7305897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_7305897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305897 prefixEnd_7305897 := by exact prefixLift 7305897
  have htrace : WordTrace (prefixWord ++ tailWord_7305897) baseStart_7305897 baseEnd_7305897 := by
    simpa [prefixWord, tailWord_7305897, baseEnd_7305897] using wordTrace_append hprefix tailTrace_7305897
  have hstable : (prefixWord ++ tailWord_7305897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305897).length < 2 ^ (prefixWord ++ tailWord_7305897).sum := by decide
  have hdescent : baseEnd_7305897 < baseStart_7305897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305934 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_7305934 : Nat := 118140960795 + 7305934 * 2 ^ 59
def prefixEnd_7305934 : Nat := 4983230072969 + 3 ^ 40 * 7305934 * 2
def baseEnd_7305934 : Nat := 416828419113924859258403

theorem tailTrace_7305934 : CollatzResearch.WordTrace tailWord_7305934 prefixEnd_7305934 416828419113924859258403 := by
  unfold tailWord_7305934
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308663039232043379190607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177646202875904231355683237 33308663039232043379190607)
  ·
    refine ⟨49962994558848065068785911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33308663039232043379190607 49962994558848065068785911)
    ·
      refine ⟨74944491838272097603178867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49962994558848065068785911 74944491838272097603178867)
      ·
        refine ⟨112416737757408146404768301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74944491838272097603178867 112416737757408146404768301)
        ·
          refine ⟨42156276659028054901788113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112416737757408146404768301 42156276659028054901788113)
          ·
            refine ⟨31617207494271041176341085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42156276659028054901788113 31617207494271041176341085)
            ·
              refine ⟨11856452810351640441127907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31617207494271041176341085 11856452810351640441127907)
              ·
                refine ⟨17784679215527460661691861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856452810351640441127907 17784679215527460661691861)
                ·
                  refine ⟨416828419113924859258403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17784679215527460661691861 416828419113924859258403)
                  ·
                    rfl

theorem cell23_7305934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_7305934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305934 prefixEnd_7305934 := by exact prefixLift 7305934
  have htrace : WordTrace (prefixWord ++ tailWord_7305934) baseStart_7305934 baseEnd_7305934 := by
    simpa [prefixWord, tailWord_7305934, baseEnd_7305934] using wordTrace_append hprefix tailTrace_7305934
  have hstable : (prefixWord ++ tailWord_7305934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305934).length < 2 ^ (prefixWord ++ tailWord_7305934).sum := by decide
  have hdescent : baseEnd_7305934 < baseStart_7305934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305974 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7305974 : Nat := 118140960795 + 7305974 * 2 ^ 59
def prefixEnd_7305974 : Nat := 4983230072969 + 3 ^ 40 * 7305974 * 2
def baseEnd_7305974 : Nat := 3751476311251503576825443

theorem tailTrace_7305974 : CollatzResearch.WordTrace tailWord_7305974 prefixEnd_7305974 3751476311251503576825443 := by
  unfold tailWord_7305974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654422702106964616561311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177647175489140955909987317 16654422702106964616561311)
  ·
    refine ⟨24981634053160446924841967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16654422702106964616561311 24981634053160446924841967)
    ·
      refine ⟨37472451079740670387262951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24981634053160446924841967 37472451079740670387262951)
      ·
        refine ⟨56208676619611005580894427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37472451079740670387262951 56208676619611005580894427)
        ·
          refine ⟨84313014929416508371341641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56208676619611005580894427 84313014929416508371341641)
          ·
            refine ⟨63234761197062381278506231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84313014929416508371341641 63234761197062381278506231)
            ·
              refine ⟨94852141795593571917759347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63234761197062381278506231 94852141795593571917759347)
              ·
                refine ⟨142278212693390357876639021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94852141795593571917759347 142278212693390357876639021)
                ·
                  refine ⟨53354329760021384203739633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142278212693390357876639021 53354329760021384203739633)
                  ·
                    refine ⟨40015747320016038152804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53354329760021384203739633 40015747320016038152804725)
                    ·
                      refine ⟨3751476311251503576825443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40015747320016038152804725 3751476311251503576825443)
                      ·
                        rfl

theorem cell23_7305974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7305974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305974 prefixEnd_7305974 := by exact prefixLift 7305974
  have htrace : WordTrace (prefixWord ++ tailWord_7305974) baseStart_7305974 baseEnd_7305974 := by
    simpa [prefixWord, tailWord_7305974, baseEnd_7305974] using wordTrace_append hprefix tailTrace_7305974
  have hstable : (prefixWord ++ tailWord_7305974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305974).length < 2 ^ (prefixWord ++ tailWord_7305974).sum := by decide
  have hdescent : baseEnd_7305974 < baseStart_7305974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305987 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_7305987 : Nat := 118140960795 + 7305987 * 2 ^ 59
def prefixEnd_7305987 : Nat := 4983230072969 + 3 ^ 40 * 7305987 * 2
def baseEnd_7305987 : Nat := 3751482986500012025962883

theorem tailTrace_7305987 : CollatzResearch.WordTrace tailWord_7305987 prefixEnd_7305987 3751482986500012025962883 := by
  unfold tailWord_7305987
  simp only [CollatzResearch.WordTrace]
  refine ⟨266471237382664337085204215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177647491588442891390136143 266471237382664337085204215)
  ·
    refine ⟨399706856073996505627806323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266471237382664337085204215 399706856073996505627806323)
    ·
      refine ⟨599560284110994758441709485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399706856073996505627806323 599560284110994758441709485)
      ·
        refine ⟨224835106541623034415641057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 599560284110994758441709485 224835106541623034415641057)
        ·
          refine ⟨168626329906217275811730793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224835106541623034415641057 168626329906217275811730793)
          ·
            refine ⟨126469747429662956858798095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168626329906217275811730793 126469747429662956858798095)
            ·
              refine ⟨189704621144494435288197143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126469747429662956858798095 189704621144494435288197143)
              ·
                refine ⟨284556931716741652932295715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189704621144494435288197143 284556931716741652932295715)
                ·
                  refine ⟨426835397575112479398443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284556931716741652932295715 426835397575112479398443573)
                  ·
                    refine ⟨40015818522666794943604085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 426835397575112479398443573 40015818522666794943604085)
                    ·
                      refine ⟨3751482986500012025962883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40015818522666794943604085 3751482986500012025962883)
                      ·
                        rfl

theorem cell23_7305987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_7305987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305987 prefixEnd_7305987 := by exact prefixLift 7305987
  have htrace : WordTrace (prefixWord ++ tailWord_7305987) baseStart_7305987 baseEnd_7305987 := by
    simpa [prefixWord, tailWord_7305987, baseEnd_7305987] using wordTrace_append hprefix tailTrace_7305987
  have hstable : (prefixWord ++ tailWord_7305987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305987).length < 2 ^ (prefixWord ++ tailWord_7305987).sum := by decide
  have hdescent : baseEnd_7305987 < baseStart_7305987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306018 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_7306018 : Nat := 118140960795 + 7306018 * 2 ^ 59
def prefixEnd_7306018 : Nat := 4983230072969 + 3 ^ 40 * 7306018 * 2
def baseEnd_7306018 : Nat := 3751498904400301404675241

theorem tailTrace_7306018 : CollatzResearch.WordTrace tailWord_7306018 prefixEnd_7306018 3751498904400301404675241 := by
  unfold tailWord_7306018
  simp only [CollatzResearch.WordTrace]
  refine ⟨66618092011388007344895677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177648245363701352919721805 66618092011388007344895677)
  ·
    refine ⟨24981784504270502754335879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66618092011388007344895677 24981784504270502754335879)
    ·
      refine ⟨37472676756405754131503819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24981784504270502754335879 37472676756405754131503819)
      ·
        refine ⟨56209015134608631197255729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37472676756405754131503819 56209015134608631197255729)
        ·
          refine ⟨42156761350956473397941797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56209015134608631197255729 42156761350956473397941797)
          ·
            refine ⟨7904392753304338762114087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42156761350956473397941797 7904392753304338762114087)
            ·
              refine ⟨11856589129956508143171131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904392753304338762114087 11856589129956508143171131)
              ·
                refine ⟨17784883694934762214756697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856589129956508143171131 17784883694934762214756697)
                ·
                  refine ⟨13338662771201071661067523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17784883694934762214756697 13338662771201071661067523)
                  ·
                    refine ⟨20007994156801607491601285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13338662771201071661067523 20007994156801607491601285)
                    ·
                      refine ⟨3751498904400301404675241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20007994156801607491601285 3751498904400301404675241)
                      ·
                        rfl

theorem cell23_7306018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_7306018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306018 prefixEnd_7306018 := by exact prefixLift 7306018
  have htrace : WordTrace (prefixWord ++ tailWord_7306018) baseStart_7306018 baseEnd_7306018 := by
    simpa [prefixWord, tailWord_7306018, baseEnd_7306018] using wordTrace_append hprefix tailTrace_7306018
  have hstable : (prefixWord ++ tailWord_7306018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306018).length < 2 ^ (prefixWord ++ tailWord_7306018).sum := by decide
  have hdescent : baseEnd_7306018 < baseStart_7306018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306024 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 8]
def baseStart_7306024 : Nat := 118140960795 + 7306024 * 2 ^ 59
def prefixEnd_7306024 : Nat := 4983230072969 + 3 ^ 40 * 7306024 * 2
def baseEnd_7306024 : Nat := 416833553920469820133357

theorem tailTrace_7306024 : CollatzResearch.WordTrace tailWord_7306024 prefixEnd_7306024 416833553920469820133357 := by
  unfold tailWord_7306024
  simp only [CollatzResearch.WordTrace]
  refine ⟨133236293441765146202150563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177648391255686861602867417 133236293441765146202150563)
  ·
    refine ⟨199854440162647719303225845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133236293441765146202150563 199854440162647719303225845)
    ·
      refine ⟨18736353765248223684677423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199854440162647719303225845 18736353765248223684677423)
      ·
        refine ⟨28104530647872335527016135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736353765248223684677423 28104530647872335527016135)
        ·
          refine ⟨42156795971808503290524203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28104530647872335527016135 42156795971808503290524203)
          ·
            refine ⟨63235193957712754935786305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42156795971808503290524203 63235193957712754935786305)
            ·
              refine ⟨47426395468284566201839729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63235193957712754935786305 47426395468284566201839729)
              ·
                refine ⟨35569796601213424651379797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47426395468284566201839729 35569796601213424651379797)
                ·
                  refine ⟨416833553920469820133357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35569796601213424651379797 416833553920469820133357)
                  ·
                    rfl

theorem cell23_7306024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_7306024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306024 prefixEnd_7306024 := by exact prefixLift 7306024
  have htrace : WordTrace (prefixWord ++ tailWord_7306024) baseStart_7306024 baseEnd_7306024 := by
    simpa [prefixWord, tailWord_7306024, baseEnd_7306024] using wordTrace_append hprefix tailTrace_7306024
  have hstable : (prefixWord ++ tailWord_7306024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306024).length < 2 ^ (prefixWord ++ tailWord_7306024).sum := by decide
  have hdescent : baseEnd_7306024 < baseStart_7306024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_7306027 : Nat := 118140960795 + 7306027 * 2 ^ 59
def prefixEnd_7306027 : Nat := 4983230072969 + 3 ^ 40 * 7306027 * 2
def baseEnd_7306027 : Nat := 3751503525726191869462699

theorem tailTrace_7306027 : CollatzResearch.WordTrace tailWord_7306027 prefixEnd_7306027 3751503525726191869462699 := by
  unfold tailWord_7306027
  simp only [CollatzResearch.WordTrace]
  refine ⟨266472696302519423916660335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177648464201679615944440223 266472696302519423916660335)
  ·
    refine ⟨399709044453779135874990503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266472696302519423916660335 399709044453779135874990503)
    ·
      refine ⟨599563566680668703812485755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399709044453779135874990503 599563566680668703812485755)
      ·
        refine ⟨899345350021003055718728633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599563566680668703812485755 899345350021003055718728633)
        ·
          refine ⟨674509012515752291789046475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899345350021003055718728633 674509012515752291789046475)
          ·
            refine ⟨1011763518773628437683569713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674509012515752291789046475 1011763518773628437683569713)
            ·
              refine ⟨758822639080221328262677285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011763518773628437683569713 758822639080221328262677285)
              ·
                refine ⟨142279244827541499049251991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758822639080221328262677285 142279244827541499049251991)
                ·
                  refine ⟨213418867241312248573877987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142279244827541499049251991 213418867241312248573877987)
                  ·
                    refine ⟨320128300861968372860816981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213418867241312248573877987 320128300861968372860816981)
                    ·
                      refine ⟨3751503525726191869462699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320128300861968372860816981 3751503525726191869462699)
                      ·
                        rfl

theorem cell23_7306027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_7306027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306027 prefixEnd_7306027 := by exact prefixLift 7306027
  have htrace : WordTrace (prefixWord ++ tailWord_7306027) baseStart_7306027 baseEnd_7306027 := by
    simpa [prefixWord, tailWord_7306027, baseEnd_7306027] using wordTrace_append hprefix tailTrace_7306027
  have hstable : (prefixWord ++ tailWord_7306027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306027).length < 2 ^ (prefixWord ++ tailWord_7306027).sum := by decide
  have hdescent : baseEnd_7306027 < baseStart_7306027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306028 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_7306028 : Nat := 118140960795 + 7306028 * 2 ^ 59
def prefixEnd_7306028 : Nat := 4983230072969 + 3 ^ 40 * 7306028 * 2
def baseEnd_7306028 : Nat := 1250501346402282121850065

theorem tailTrace_7306028 : CollatzResearch.WordTrace tailWord_7306028 prefixEnd_7306028 1250501346402282121850065 := by
  unfold tailWord_7306028
  simp only [CollatzResearch.WordTrace]
  refine ⟨133236366387757900543723369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177648488517010534058297825 133236366387757900543723369)
  ·
    refine ⟨99927274790818425407792527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133236366387757900543723369 99927274790818425407792527)
    ·
      refine ⟨149890912186227638111688791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99927274790818425407792527 149890912186227638111688791)
      ·
        refine ⟨224836368279341457167533187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149890912186227638111688791 224836368279341457167533187)
        ·
          refine ⟨337254552419012185751299781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224836368279341457167533187 337254552419012185751299781)
          ·
            refine ⟨63235228578564784828368709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337254552419012185751299781 63235228578564784828368709)
            ·
              refine ⟨11856605358480897155319133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63235228578564784828368709 11856605358480897155319133)
              ·
                refine ⟨4446227009430336433244675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11856605358480897155319133 4446227009430336433244675)
                ·
                  refine ⟨6669340514145504649867013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446227009430336433244675 6669340514145504649867013)
                  ·
                    refine ⟨1250501346402282121850065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669340514145504649867013 1250501346402282121850065)
                    ·
                      rfl

theorem cell23_7306028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_7306028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306028 prefixEnd_7306028 := by exact prefixLift 7306028
  have htrace : WordTrace (prefixWord ++ tailWord_7306028) baseStart_7306028 baseEnd_7306028 := by
    simpa [prefixWord, tailWord_7306028, baseEnd_7306028] using wordTrace_append hprefix tailTrace_7306028
  have hstable : (prefixWord ++ tailWord_7306028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306028).length < 2 ^ (prefixWord ++ tailWord_7306028).sum := by decide
  have hdescent : baseEnd_7306028 < baseStart_7306028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306071 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 1, 5]
def baseStart_7306071 : Nat := 118140960795 + 7306071 * 2 ^ 59
def prefixEnd_7306071 : Nat := 4983230072969 + 3 ^ 40 * 7306071 * 2
def baseEnd_7306071 : Nat := 1250508706291663232437499

theorem tailTrace_7306071 : CollatzResearch.WordTrace tailWord_7306071 prefixEnd_7306071 1250508706291663232437499 := by
  unfold tailWord_7306071
  simp only [CollatzResearch.WordTrace]
  refine ⟨266474301114360019431262067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177649534076240012954174711 266474301114360019431262067)
  ·
    refine ⟨399711451671540029146893101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266474301114360019431262067 399711451671540029146893101)
    ·
      refine ⟨149891794376827510930084913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399711451671540029146893101 149891794376827510930084913)
      ·
        refine ⟨112418845782620633197563685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149891794376827510930084913 112418845782620633197563685)
        ·
          refine ⟨21078533584241368724543191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112418845782620633197563685 21078533584241368724543191)
          ·
            refine ⟨31617800376362053086814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21078533584241368724543191 31617800376362053086814787)
            ·
              refine ⟨47426700564543079630222181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31617800376362053086814787 47426700564543079630222181)
              ·
                refine ⟨8892506355851827430666659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47426700564543079630222181 8892506355851827430666659)
                ·
                  refine ⟨13338759533777741145999989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892506355851827430666659 13338759533777741145999989)
                  ·
                    refine ⟨1250508706291663232437499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13338759533777741145999989 1250508706291663232437499)
                    ·
                      rfl

theorem cell23_7306071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_7306071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306071 prefixEnd_7306071 := by exact prefixLift 7306071
  have htrace : WordTrace (prefixWord ++ tailWord_7306071) baseStart_7306071 baseEnd_7306071 := by
    simpa [prefixWord, tailWord_7306071, baseEnd_7306071] using wordTrace_append hprefix tailTrace_7306071
  have hstable : (prefixWord ++ tailWord_7306071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306071).length < 2 ^ (prefixWord ++ tailWord_7306071).sum := by decide
  have hdescent : baseEnd_7306071 < baseStart_7306071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306085 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7306085 : Nat := 118140960795 + 7306085 * 2 ^ 59
def prefixEnd_7306085 : Nat := 4983230072969 + 3 ^ 40 * 7306085 * 2
def baseEnd_7306085 : Nat := 3751533307604152642537433

theorem tailTrace_7306085 : CollatzResearch.WordTrace tailWord_7306085 prefixEnd_7306085 3751533307604152642537433 := by
  unfold tailWord_7306085
  simp only [CollatzResearch.WordTrace]
  refine ⟨266474811736309299822271709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177649874490872866548181139 266474811736309299822271709)
  ·
    refine ⟨99928054401115987433351891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266474811736309299822271709 99928054401115987433351891)
    ·
      refine ⟨149892081601673981150027837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99928054401115987433351891 149892081601673981150027837)
      ·
        refine ⟨56209530600627742931260439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149892081601673981150027837 56209530600627742931260439)
        ·
          refine ⟨84314295900941614396890659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56209530600627742931260439 84314295900941614396890659)
          ·
            refine ⟨126471443851412421595335989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84314295900941614396890659 126471443851412421595335989)
            ·
              refine ⟨11856697861069914524562749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126471443851412421595335989 11856697861069914524562749)
              ·
                refine ⟨4446261697901217946711031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11856697861069914524562749 4446261697901217946711031)
                ·
                  refine ⟨6669392546851826920066547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446261697901217946711031 6669392546851826920066547)
                  ·
                    refine ⟨10004088820277740380099821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669392546851826920066547 10004088820277740380099821)
                    ·
                      refine ⟨3751533307604152642537433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004088820277740380099821 3751533307604152642537433)
                      ·
                        rfl

theorem cell23_7306085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7306085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306085 prefixEnd_7306085 := by exact prefixLift 7306085
  have htrace : WordTrace (prefixWord ++ tailWord_7306085) baseStart_7306085 baseEnd_7306085 := by
    simpa [prefixWord, tailWord_7306085, baseEnd_7306085] using wordTrace_append hprefix tailTrace_7306085
  have hstable : (prefixWord ++ tailWord_7306085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306085).length < 2 ^ (prefixWord ++ tailWord_7306085).sum := by decide
  have hdescent : baseEnd_7306085 < baseStart_7306085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306091 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 4]
def baseStart_7306091 : Nat := 118140960795 + 7306091 * 2 ^ 59
def prefixEnd_7306091 : Nat := 4983230072969 + 3 ^ 40 * 7306091 * 2
def baseEnd_7306091 : Nat := 3751536388488079619062405

theorem tailTrace_7306091 : CollatzResearch.WordTrace tailWord_7306091 prefixEnd_7306091 3751536388488079619062405 := by
  unfold tailWord_7306091
  simp only [CollatzResearch.WordTrace]
  refine ⟨266475030574287562846990127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177650020382858375231326751 266475030574287562846990127)
  ·
    refine ⟨399712545861431344270485191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266475030574287562846990127 399712545861431344270485191)
    ·
      refine ⟨599568818792147016405727787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399712545861431344270485191 599568818792147016405727787)
      ·
        refine ⟨899353228188220524608591681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599568818792147016405727787 899353228188220524608591681)
        ·
          refine ⟨674514921141165393456443761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899353228188220524608591681 674514921141165393456443761)
          ·
            refine ⟨505886190855874045092332821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674514921141165393456443761 505886190855874045092332821)
            ·
              refine ⟨23713415196369095863703101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 505886190855874045092332821 23713415196369095863703101)
              ·
                refine ⟨8892530698638410948888663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23713415196369095863703101 8892530698638410948888663)
                ·
                  refine ⟨13338796047957616423332995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892530698638410948888663 13338796047957616423332995)
                  ·
                    refine ⟨20008194071936424634999493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13338796047957616423332995 20008194071936424634999493)
                    ·
                      refine ⟨3751536388488079619062405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20008194071936424634999493 3751536388488079619062405)
                      ·
                        rfl

theorem cell23_7306091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 4].length) (baseStart_7306091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306091 prefixEnd_7306091 := by exact prefixLift 7306091
  have htrace : WordTrace (prefixWord ++ tailWord_7306091) baseStart_7306091 baseEnd_7306091 := by
    simpa [prefixWord, tailWord_7306091, baseEnd_7306091] using wordTrace_append hprefix tailTrace_7306091
  have hstable : (prefixWord ++ tailWord_7306091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306091).length < 2 ^ (prefixWord ++ tailWord_7306091).sum := by decide
  have hdescent : baseEnd_7306091 < baseStart_7306091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306102 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7306102 : Nat := 118140960795 + 7306102 * 2 ^ 59
def prefixEnd_7306102 : Nat := 4983230072969 + 3 ^ 40 * 7306102 * 2
def baseEnd_7306102 : Nat := 3751542036775279076024855

theorem tailTrace_7306102 : CollatzResearch.WordTrace tailWord_7306102 prefixEnd_7306102 3751542036775279076024855 := by
  unfold tailWord_7306102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654714486077981982852535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177650287851498474483760373 16654714486077981982852535)
  ·
    refine ⟨24982071729116972974278803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16654714486077981982852535 24982071729116972974278803)
    ·
      refine ⟨37473107593675459461418205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24982071729116972974278803 37473107593675459461418205)
      ·
        refine ⟨14052415347628297298031827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37473107593675459461418205 14052415347628297298031827)
        ·
          refine ⟨21078623021442445947047741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14052415347628297298031827 21078623021442445947047741)
          ·
            refine ⟨7904483633040917230142903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21078623021442445947047741 7904483633040917230142903)
            ·
              refine ⟨11856725449561375845214355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904483633040917230142903 11856725449561375845214355)
              ·
                refine ⟨17785088174342063767821533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856725449561375845214355 17785088174342063767821533)
                ·
                  refine ⟨6669408065378273912933075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17785088174342063767821533 6669408065378273912933075)
                  ·
                    refine ⟨10004112098067410869399613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669408065378273912933075 10004112098067410869399613)
                    ·
                      refine ⟨3751542036775279076024855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004112098067410869399613 3751542036775279076024855)
                      ·
                        rfl

theorem cell23_7306102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7306102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306102 prefixEnd_7306102 := by exact prefixLift 7306102
  have htrace : WordTrace (prefixWord ++ tailWord_7306102) baseStart_7306102 baseEnd_7306102 := by
    simpa [prefixWord, tailWord_7306102, baseEnd_7306102] using wordTrace_append hprefix tailTrace_7306102
  have hstable : (prefixWord ++ tailWord_7306102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306102).length < 2 ^ (prefixWord ++ tailWord_7306102).sum := by decide
  have hdescent : baseEnd_7306102 < baseStart_7306102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306104 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_7306104 : Nat := 118140960795 + 7306104 * 2 ^ 59
def prefixEnd_7306104 : Nat := 4983230072969 + 3 ^ 40 * 7306104 * 2
def baseEnd_7306104 : Nat := 3751543063736588068199845

theorem tailTrace_7306104 : CollatzResearch.WordTrace tailWord_7306104 prefixEnd_7306104 3751543063736588068199845 := by
  unfold tailWord_7306104
  simp only [CollatzResearch.WordTrace]
  refine ⟨133237752361620233033606683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177650336482160310711475577 133237752361620233033606683)
  ·
    refine ⟨199856628542430349550410025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133237752361620233033606683 199856628542430349550410025)
    ·
      refine ⟨149892471406822762162807519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199856628542430349550410025 149892471406822762162807519)
      ·
        refine ⟨224838707110234143244211279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149892471406822762162807519 224838707110234143244211279)
        ·
          refine ⟨337258060665351214866316919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224838707110234143244211279 337258060665351214866316919)
          ·
            refine ⟨505887090998026822299475379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337258060665351214866316919 505887090998026822299475379)
            ·
              refine ⟨758830636497040233449213069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505887090998026822299475379 758830636497040233449213069)
              ·
                refine ⟨284561488686390087543454901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758830636497040233449213069 284561488686390087543454901)
                ·
                  refine ⟨26677639564349070707198897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284561488686390087543454901 26677639564349070707198897)
                  ·
                    refine ⟨20008229673261803030399173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26677639564349070707198897 20008229673261803030399173)
                    ·
                      refine ⟨3751543063736588068199845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20008229673261803030399173 3751543063736588068199845)
                      ·
                        rfl

theorem cell23_7306104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_7306104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306104 prefixEnd_7306104 := by exact prefixLift 7306104
  have htrace : WordTrace (prefixWord ++ tailWord_7306104) baseStart_7306104 baseEnd_7306104 := by
    simpa [prefixWord, tailWord_7306104, baseEnd_7306104] using wordTrace_append hprefix tailTrace_7306104
  have hstable : (prefixWord ++ tailWord_7306104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306104).length < 2 ^ (prefixWord ++ tailWord_7306104).sum := by decide
  have hdescent : baseEnd_7306104 < baseStart_7306104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306138 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7306138 : Nat := 118140960795 + 7306138 * 2 ^ 59
def prefixEnd_7306138 : Nat := 4983230072969 + 3 ^ 40 * 7306138 * 2
def baseEnd_7306138 : Nat := 3751560522078840935174689

theorem tailTrace_7306138 : CollatzResearch.WordTrace tailWord_7306138 prefixEnd_7306138 3751560522078840935174689 := by
  unfold tailWord_7306138
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619186201279322468487767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177651163203411526582634045 66619186201279322468487767)
  ·
    refine ⟨99928779301918983702731651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66619186201279322468487767 99928779301918983702731651)
    ·
      refine ⟨149893168952878475554097477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99928779301918983702731651 149893168952878475554097477)
      ·
        refine ⟨28104969178664714166393277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149893168952878475554097477 28104969178664714166393277)
        ·
          refine ⟨10539363441999267812397479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28104969178664714166393277 10539363441999267812397479)
          ·
            refine ⟨15809045162998901718596219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10539363441999267812397479 15809045162998901718596219)
            ·
              refine ⟨23713567744498352577894329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15809045162998901718596219 23713567744498352577894329)
              ·
                refine ⟨17785175808373764433420747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23713567744498352577894329 17785175808373764433420747)
                ·
                  refine ⟨26677763712560646650131121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17785175808373764433420747 26677763712560646650131121)
                  ·
                    refine ⟨20008322784420484987598341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26677763712560646650131121 20008322784420484987598341)
                    ·
                      refine ⟨3751560522078840935174689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20008322784420484987598341 3751560522078840935174689)
                      ·
                        rfl

theorem cell23_7306138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7306138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306138 prefixEnd_7306138 := by exact prefixLift 7306138
  have htrace : WordTrace (prefixWord ++ tailWord_7306138) baseStart_7306138 baseEnd_7306138 := by
    simpa [prefixWord, tailWord_7306138, baseEnd_7306138] using wordTrace_append hprefix tailTrace_7306138
  have hstable : (prefixWord ++ tailWord_7306138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306138).length < 2 ^ (prefixWord ++ tailWord_7306138).sum := by decide
  have hdescent : baseEnd_7306138 < baseStart_7306138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306168 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_7306168 : Nat := 118140960795 + 7306168 * 2 ^ 59
def prefixEnd_7306168 : Nat := 4983230072969 + 3 ^ 40 * 7306168 * 2
def baseEnd_7306168 : Nat := 3751575926498475817799551

theorem tailTrace_7306168 : CollatzResearch.WordTrace tailWord_7306168 prefixEnd_7306168 3751575926498475817799551 := by
  unfold tailWord_7306168
  simp only [CollatzResearch.WordTrace]
  refine ⟨133238919497504302498771579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177651892663339069998362105 133238919497504302498771579)
  ·
    refine ⟨199858379246256453748157369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133238919497504302498771579 199858379246256453748157369)
    ·
      refine ⟨149893784434692340311118027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199858379246256453748157369 149893784434692340311118027)
      ·
        refine ⟨224840676652038510466677041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149893784434692340311118027 224840676652038510466677041)
        ·
          refine ⟨168630507489028882850007781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224840676652038510466677041 168630507489028882850007781)
          ·
            refine ⟨31618220154192915534376459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168630507489028882850007781 31618220154192915534376459)
            ·
              refine ⟨47427330231289373301564689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31618220154192915534376459 47427330231289373301564689)
              ·
                refine ⟨35570497673467029976173517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47427330231289373301564689 35570497673467029976173517)
                ·
                  refine ⟨13338936627550136241065069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35570497673467029976173517 13338936627550136241065069)
                  ·
                    refine ⟨5002101235331301090399401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13338936627550136241065069 5002101235331301090399401)
                    ·
                      refine ⟨3751575926498475817799551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002101235331301090399401 3751575926498475817799551)
                      ·
                        rfl

theorem cell23_7306168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_7306168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306168 prefixEnd_7306168 := by exact prefixLift 7306168
  have htrace : WordTrace (prefixWord ++ tailWord_7306168) baseStart_7306168 baseEnd_7306168 := by
    simpa [prefixWord, tailWord_7306168, baseEnd_7306168] using wordTrace_append hprefix tailTrace_7306168
  have hstable : (prefixWord ++ tailWord_7306168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306168).length < 2 ^ (prefixWord ++ tailWord_7306168).sum := by decide
  have hdescent : baseEnd_7306168 < baseStart_7306168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306202 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_7306202 : Nat := 118140960795 + 7306202 * 2 ^ 59
def prefixEnd_7306202 : Nat := 4983230072969 + 3 ^ 40 * 7306202 * 2
def baseEnd_7306202 : Nat := 3751593384840728684774395

theorem tailTrace_7306202 : CollatzResearch.WordTrace tailWord_7306202 prefixEnd_7306202 3751593384840728684774395 := by
  unfold tailWord_7306202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619769769221357201070215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177652719384590285869520573 66619769769221357201070215)
  ·
    refine ⟨99929654653832035801605323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66619769769221357201070215 99929654653832035801605323)
    ·
      refine ⟨149894481980748053702407985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99929654653832035801605323 149894481980748053702407985)
      ·
        refine ⟨112420861485561040276805989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149894481980748053702407985 112420861485561040276805989)
        ·
          refine ⟨21078911528542695051901123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112420861485561040276805989 21078911528542695051901123)
          ·
            refine ⟨31618367292814042577851685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21078911528542695051901123 31618367292814042577851685)
            ·
              refine ⟨5928443867402632983347191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31618367292814042577851685 5928443867402632983347191)
              ·
                refine ⟨8892665801103949475020787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928443867402632983347191 8892665801103949475020787)
                ·
                  refine ⟨13338998701655924212531181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892665801103949475020787 13338998701655924212531181)
                  ·
                    refine ⟨5002124513120971579699193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13338998701655924212531181 5002124513120971579699193)
                    ·
                      refine ⟨3751593384840728684774395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002124513120971579699193 3751593384840728684774395)
                      ·
                        rfl

theorem cell23_7306202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_7306202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306202 prefixEnd_7306202 := by exact prefixLift 7306202
  have htrace : WordTrace (prefixWord ++ tailWord_7306202) baseStart_7306202 baseEnd_7306202 := by
    simpa [prefixWord, tailWord_7306202, baseEnd_7306202] using wordTrace_append hprefix tailTrace_7306202
  have hstable : (prefixWord ++ tailWord_7306202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306202).length < 2 ^ (prefixWord ++ tailWord_7306202).sum := by decide
  have hdescent : baseEnd_7306202 < baseStart_7306202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306211 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7306211 : Nat := 118140960795 + 7306211 * 2 ^ 59
def prefixEnd_7306211 : Nat := 4983230072969 + 3 ^ 40 * 7306211 * 2
def baseEnd_7306211 : Nat := 3751598006166619149561853

theorem tailTrace_7306211 : CollatzResearch.WordTrace tailWord_7306211 prefixEnd_7306211 3751598006166619149561853 := by
  unfold tailWord_7306211
  simp only [CollatzResearch.WordTrace]
  refine ⟨266479407333852823341358487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177652938222568548894238991 266479407333852823341358487)
  ·
    refine ⟨399719111000779235012037731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266479407333852823341358487 399719111000779235012037731)
    ·
      refine ⟨599578666501168852518056597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399719111000779235012037731 599578666501168852518056597)
      ·
        refine ⟨28105249992242289961783903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 599578666501168852518056597 28105249992242289961783903)
        ·
          refine ⟨42157874988363434942675855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28105249992242289961783903 42157874988363434942675855)
          ·
            refine ⟨63236812482545152414013783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42157874988363434942675855 63236812482545152414013783)
            ·
              refine ⟨94855218723817728621020675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63236812482545152414013783 94855218723817728621020675)
              ·
                refine ⟨142282828085726592931531013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94855218723817728621020675 142282828085726592931531013)
                ·
                  refine ⟨26678030266073736174662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142282828085726592931531013 26678030266073736174662065)
                  ·
                    refine ⟨20008522699555302130996549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26678030266073736174662065 20008522699555302130996549)
                    ·
                      refine ⟨3751598006166619149561853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20008522699555302130996549 3751598006166619149561853)
                      ·
                        rfl

theorem cell23_7306211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7306211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306211 prefixEnd_7306211 := by exact prefixLift 7306211
  have htrace : WordTrace (prefixWord ++ tailWord_7306211) baseStart_7306211 baseEnd_7306211 := by
    simpa [prefixWord, tailWord_7306211, baseEnd_7306211] using wordTrace_append hprefix tailTrace_7306211
  have hstable : (prefixWord ++ tailWord_7306211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306211).length < 2 ^ (prefixWord ++ tailWord_7306211).sum := by decide
  have hdescent : baseEnd_7306211 < baseStart_7306211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306251 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 7]
def baseStart_7306251 : Nat := 118140960795 + 7306251 * 2 ^ 59
def prefixEnd_7306251 : Nat := 4983230072969 + 3 ^ 40 * 7306251 * 2
def baseEnd_7306251 : Nat := 1250539515130932997687223

theorem tailTrace_7306251 : CollatzResearch.WordTrace tailWord_7306251 prefixEnd_7306251 1250539515130932997687223 := by
  unfold tailWord_7306251
  simp only [CollatzResearch.WordTrace]
  refine ⟨266480866253707910172814607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177653910835805273448543071 266480866253707910172814607)
  ·
    refine ⟨399721299380561865259221911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266480866253707910172814607 399721299380561865259221911)
    ·
      refine ⟨599581949070842797888832867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399721299380561865259221911 599581949070842797888832867)
      ·
        refine ⟨899372923606264196833249301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599581949070842797888832867 899372923606264196833249301)
        ·
          refine ⟨42158105794043634226558561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 899372923606264196833249301 42158105794043634226558561)
          ·
            refine ⟨31618579345532725669918921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42158105794043634226558561 31618579345532725669918921)
            ·
              refine ⟨23713934509149544252439191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31618579345532725669918921 23713934509149544252439191)
              ·
                refine ⟨35570901763724316378658787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23713934509149544252439191 35570901763724316378658787)
                ·
                  refine ⟨53356352645586474567988181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35570901763724316378658787 53356352645586474567988181)
                  ·
                    refine ⟨1250539515130932997687223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53356352645586474567988181 1250539515130932997687223)
                    ·
                      rfl

theorem cell23_7306251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_7306251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306251 prefixEnd_7306251 := by exact prefixLift 7306251
  have htrace : WordTrace (prefixWord ++ tailWord_7306251) baseStart_7306251 baseEnd_7306251 := by
    simpa [prefixWord, tailWord_7306251, baseEnd_7306251] using wordTrace_append hprefix tailTrace_7306251
  have hstable : (prefixWord ++ tailWord_7306251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306251).length < 2 ^ (prefixWord ++ tailWord_7306251).sum := by decide
  have hdescent : baseEnd_7306251 < baseStart_7306251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306272 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 7]
def baseStart_7306272 : Nat := 118140960795 + 7306272 * 2 ^ 59
def prefixEnd_7306272 : Nat := 4983230072969 + 3 ^ 40 * 7306272 * 2
def baseEnd_7306272 : Nat := 416847703165171490099897

theorem tailTrace_7306272 : CollatzResearch.WordTrace tailWord_7306272 prefixEnd_7306272 416847703165171490099897 := by
  unfold tailWord_7306272
  simp only [CollatzResearch.WordTrace]
  refine ⟨133240816093315915379664535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177654421457754553839552713 133240816093315915379664535)
  ·
    refine ⟨199861224139973873069496803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133240816093315915379664535 199861224139973873069496803)
    ·
      refine ⟨299791836209960809604245205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199861224139973873069496803 299791836209960809604245205)
      ·
        refine ⟨7026371161170956475099497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 299791836209960809604245205 7026371161170956475099497)
        ·
          refine ⟨5269778370878217356324623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026371161170956475099497 5269778370878217356324623)
          ·
            refine ⟨7904667556317326034486935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269778370878217356324623 7904667556317326034486935)
            ·
              refine ⟨11857001334475989051730403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904667556317326034486935 11857001334475989051730403)
              ·
                refine ⟨17785502001713983577595605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857001334475989051730403 17785502001713983577595605)
                ·
                  refine ⟨416847703165171490099897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17785502001713983577595605 416847703165171490099897)
                  ·
                    rfl

theorem cell23_7306272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_7306272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306272 prefixEnd_7306272 := by exact prefixLift 7306272
  have htrace : WordTrace (prefixWord ++ tailWord_7306272) baseStart_7306272 baseEnd_7306272 := by
    simpa [prefixWord, tailWord_7306272, baseEnd_7306272] using wordTrace_append hprefix tailTrace_7306272
  have hstable : (prefixWord ++ tailWord_7306272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306272).length < 2 ^ (prefixWord ++ tailWord_7306272).sum := by decide
  have hdescent : baseEnd_7306272 < baseStart_7306272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306288 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2]
def baseStart_7306288 : Nat := 118140960795 + 7306288 * 2 ^ 59
def prefixEnd_7306288 : Nat := 4983230072969 + 3 ^ 40 * 7306288 * 2
def baseEnd_7306288 : Nat := 3751637544177015348298999

theorem tailTrace_7306288 : CollatzResearch.WordTrace tailWord_7306288 prefixEnd_7306288 3751637544177015348298999 := by
  unfold tailWord_7306288
  simp only [CollatzResearch.WordTrace]
  refine ⟨133241107877286932745955759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177654810503049243661274345 133241107877286932745955759)
  ·
    refine ⟨199861661815930399118933639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133241107877286932745955759 199861661815930399118933639)
    ·
      refine ⟨299792492723895598678400459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199861661815930399118933639 299792492723895598678400459)
      ·
        refine ⟨449688739085843398017600689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299792492723895598678400459 449688739085843398017600689)
        ·
          refine ⟨337266554314382548513200517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449688739085843398017600689 337266554314382548513200517)
          ·
            refine ⟨63237478933946727846225097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337266554314382548513200517 63237478933946727846225097)
            ·
              refine ⟨47428109200460045884668823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63237478933946727846225097 47428109200460045884668823)
              ·
                refine ⟨71142163800690068827003235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47428109200460045884668823 71142163800690068827003235)
                ·
                  refine ⟨106713245701035103240504853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71142163800690068827003235 106713245701035103240504853)
                  ·
                    refine ⟨5002183392236020464398665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106713245701035103240504853 5002183392236020464398665)
                    ·
                      refine ⟨3751637544177015348298999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002183392236020464398665 3751637544177015348298999)
                      ·
                        rfl

theorem cell23_7306288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2].length) (baseStart_7306288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306288 prefixEnd_7306288 := by exact prefixLift 7306288
  have htrace : WordTrace (prefixWord ++ tailWord_7306288) baseStart_7306288 baseEnd_7306288 := by
    simpa [prefixWord, tailWord_7306288, baseEnd_7306288] using wordTrace_append hprefix tailTrace_7306288
  have hstable : (prefixWord ++ tailWord_7306288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306288).length < 2 ^ (prefixWord ++ tailWord_7306288).sum := by decide
  have hdescent : baseEnd_7306288 < baseStart_7306288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306298 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_7306298 : Nat := 118140960795 + 7306298 * 2 ^ 59
def prefixEnd_7306298 : Nat := 4983230072969 + 3 ^ 40 * 7306298 * 2
def baseEnd_7306298 : Nat := 1250547559661186769724651

theorem tailTrace_7306298 : CollatzResearch.WordTrace tailWord_7306298 prefixEnd_7306298 1250547559661186769724651 := by
  unfold tailWord_7306298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66620645121134409299943887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177655053656358424799850365 66620645121134409299943887)
  ·
    refine ⟨99930967681701613949915831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66620645121134409299943887 99930967681701613949915831)
    ·
      refine ⟨149896451522552420924873747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99930967681701613949915831 149896451522552420924873747)
      ·
        refine ⟨224844677283828631387310621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149896451522552420924873747 224844677283828631387310621)
        ·
          refine ⟨84316753981435736770241483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224844677283828631387310621 84316753981435736770241483)
          ·
            refine ⟨126475130972153605155362225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84316753981435736770241483 126475130972153605155362225)
            ·
              refine ⟨94856348229115203866521669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126475130972153605155362225 94856348229115203866521669)
              ·
                refine ⟨17785565292959100724972813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94856348229115203866521669 17785565292959100724972813)
                ·
                  refine ⟨6669586984859662771864805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17785565292959100724972813 6669586984859662771864805)
                  ·
                    refine ⟨1250547559661186769724651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669586984859662771864805 1250547559661186769724651)
                    ·
                      rfl

theorem cell23_7306298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_7306298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306298 prefixEnd_7306298 := by exact prefixLift 7306298
  have htrace : WordTrace (prefixWord ++ tailWord_7306298) baseStart_7306298 baseEnd_7306298 := by
    simpa [prefixWord, tailWord_7306298, baseEnd_7306298] using wordTrace_append hprefix tailTrace_7306298
  have hstable : (prefixWord ++ tailWord_7306298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306298).length < 2 ^ (prefixWord ++ tailWord_7306298).sum := by decide
  have hdescent : baseEnd_7306298 < baseStart_7306298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306328 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 6]
def baseStart_7306328 : Nat := 118140960795 + 7306328 * 2 ^ 59
def prefixEnd_7306328 : Nat := 4983230072969 + 3 ^ 40 * 7306328 * 2
def baseEnd_7306328 : Nat := 416850898155910576866535

theorem tailTrace_7306328 : CollatzResearch.WordTrace tailWord_7306328 prefixEnd_7306328 416850898155910576866535 := by
  unfold tailWord_7306328
  simp only [CollatzResearch.WordTrace]
  refine ⟨133241837337214476161683819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177655783116285968215578425 133241837337214476161683819)
  ·
    refine ⟨199862756005821714242525729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133241837337214476161683819 199862756005821714242525729)
    ·
      refine ⟨149897067004366285681894297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199862756005821714242525729 149897067004366285681894297)
      ·
        refine ⟨112422800253274714261420723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149897067004366285681894297 112422800253274714261420723)
        ·
          refine ⟨168634200379912071392131085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112422800253274714261420723 168634200379912071392131085)
          ·
            refine ⟨63237825142467026772049157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168634200379912071392131085 63237825142467026772049157)
            ·
              refine ⟨11857092214212567519759217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63237825142467026772049157 11857092214212567519759217)
              ·
                refine ⟨8892819160659425639819413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857092214212567519759217 8892819160659425639819413)
                ·
                  refine ⟨416850898155910576866535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8892819160659425639819413 416850898155910576866535)
                  ·
                    rfl

theorem cell23_7306328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_7306328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306328 prefixEnd_7306328 := by exact prefixLift 7306328
  have htrace : WordTrace (prefixWord ++ tailWord_7306328) baseStart_7306328 baseEnd_7306328 := by
    simpa [prefixWord, tailWord_7306328, baseEnd_7306328] using wordTrace_append hprefix tailTrace_7306328
  have hstable : (prefixWord ++ tailWord_7306328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306328).length < 2 ^ (prefixWord ++ tailWord_7306328).sum := by decide
  have hdescent : baseEnd_7306328 < baseStart_7306328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306332 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7306332 : Nat := 118140960795 + 7306332 * 2 ^ 59
def prefixEnd_7306332 : Nat := 4983230072969 + 3 ^ 40 * 7306332 * 2
def baseEnd_7306332 : Nat := 1250553379108604392049599

theorem tailTrace_7306332 : CollatzResearch.WordTrace tailWord_7306332 prefixEnd_7306332 1250553379108604392049599 := by
  unfold tailWord_7306332
  simp only [CollatzResearch.WordTrace]
  refine ⟨133241910283207230503256625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177655880377609640671008833 133241910283207230503256625)
  ·
    refine ⟨99931432712405422877442469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133241910283207230503256625 99931432712405422877442469)
    ·
      refine ⟨18737143633576016789520463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99931432712405422877442469 18737143633576016789520463)
      ·
        refine ⟨28105715450364025184280695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18737143633576016789520463 28105715450364025184280695)
        ·
          refine ⟨42158573175546037776421043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28105715450364025184280695 42158573175546037776421043)
          ·
            refine ⟨63237859763319056664631565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42158573175546037776421043 63237859763319056664631565)
            ·
              refine ⟨23714197411244646249236837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63237859763319056664631565 23714197411244646249236837)
              ·
                refine ⟨4446412014608371171731907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23714197411244646249236837 4446412014608371171731907)
                ·
                  refine ⟨6669618021912556757597861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446412014608371171731907 6669618021912556757597861)
                  ·
                    refine ⟨1250553379108604392049599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669618021912556757597861 1250553379108604392049599)
                    ·
                      rfl

theorem cell23_7306332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7306332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306332 prefixEnd_7306332 := by exact prefixLift 7306332
  have htrace : WordTrace (prefixWord ++ tailWord_7306332) baseStart_7306332 baseEnd_7306332 := by
    simpa [prefixWord, tailWord_7306332, baseEnd_7306332] using wordTrace_append hprefix tailTrace_7306332
  have hstable : (prefixWord ++ tailWord_7306332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306332).length < 2 ^ (prefixWord ++ tailWord_7306332).sum := by decide
  have hdescent : baseEnd_7306332 < baseStart_7306332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306351 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_7306351 : Nat := 118140960795 + 7306351 * 2 ^ 59
def prefixEnd_7306351 : Nat := 4983230072969 + 3 ^ 40 * 7306351 * 2
def baseEnd_7306351 : Nat := 3751669893458248601811209

theorem tailTrace_7306351 : CollatzResearch.WordTrace tailWord_7306351 prefixEnd_7306351 3751669893458248601811209 := by
  unfold tailWord_7306351
  simp only [CollatzResearch.WordTrace]
  refine ⟨266484513553345627251454907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177656342368897084834303271 266484513553345627251454907)
  ·
    refine ⟨399726770330018440877182361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266484513553345627251454907 399726770330018440877182361)
    ·
      refine ⟨299795077747513830657886771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399726770330018440877182361 299795077747513830657886771)
      ·
        refine ⟨449692616621270745986830157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299795077747513830657886771 449692616621270745986830157)
        ·
          refine ⟨168634731232976529745061309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449692616621270745986830157 168634731232976529745061309)
          ·
            refine ⟨63238024212366198654397991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168634731232976529745061309 63238024212366198654397991)
            ·
              refine ⟨94857036318549297981596987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63238024212366198654397991 94857036318549297981596987)
              ·
                refine ⟨142285554477823946972395481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94857036318549297981596987 142285554477823946972395481)
                ·
                  refine ⟨106714165858367960229296611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142285554477823946972395481 106714165858367960229296611)
                  ·
                    refine ⟨160071248787551940343944917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106714165858367960229296611 160071248787551940343944917)
                    ·
                      refine ⟨3751669893458248601811209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160071248787551940343944917 3751669893458248601811209)
                      ·
                        rfl

theorem cell23_7306351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_7306351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306351 prefixEnd_7306351 := by exact prefixLift 7306351
  have htrace : WordTrace (prefixWord ++ tailWord_7306351) baseStart_7306351 baseEnd_7306351 := by
    simpa [prefixWord, tailWord_7306351, baseEnd_7306351] using wordTrace_append hprefix tailTrace_7306351
  have hstable : (prefixWord ++ tailWord_7306351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306351).length < 2 ^ (prefixWord ++ tailWord_7306351).sum := by decide
  have hdescent : baseEnd_7306351 < baseStart_7306351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306365 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_7306365 : Nat := 118140960795 + 7306365 * 2 ^ 59
def prefixEnd_7306365 : Nat := 4983230072969 + 3 ^ 40 * 7306365 * 2
def baseEnd_7306365 : Nat := 3751677082187411547036145

theorem tailTrace_7306365 : CollatzResearch.WordTrace tailWord_7306365 prefixEnd_7306365 3751677082187411547036145 := by
  unfold tailWord_7306365
  simp only [CollatzResearch.WordTrace]
  refine ⟨266485024175294907642464549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177656682783529938428309699 266485024175294907642464549)
  ·
    refine ⟨49965942032867795182962103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266485024175294907642464549 49965942032867795182962103)
    ·
      refine ⟨74948913049301692774443155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49965942032867795182962103 74948913049301692774443155)
      ·
        refine ⟨112423369573952539161664733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74948913049301692774443155 112423369573952539161664733)
        ·
          refine ⟨42158763590232202185624275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112423369573952539161664733 42158763590232202185624275)
          ·
            refine ⟨63238145385348303278436413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42158763590232202185624275 63238145385348303278436413)
            ·
              refine ⟨23714304519505613729413655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63238145385348303278436413 23714304519505613729413655)
              ·
                refine ⟨35571456779258420594120483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23714304519505613729413655 35571456779258420594120483)
                ·
                  refine ⟨53357185168887630891180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35571456779258420594120483 53357185168887630891180725)
                  ·
                    refine ⟨5002236109583215396048193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53357185168887630891180725 5002236109583215396048193)
                    ·
                      refine ⟨3751677082187411547036145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002236109583215396048193 3751677082187411547036145)
                      ·
                        rfl

theorem cell23_7306365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_7306365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306365 prefixEnd_7306365 := by exact prefixLift 7306365
  have htrace : WordTrace (prefixWord ++ tailWord_7306365) baseStart_7306365 baseEnd_7306365 := by
    simpa [prefixWord, tailWord_7306365, baseEnd_7306365] using wordTrace_append hprefix tailTrace_7306365
  have hstable : (prefixWord ++ tailWord_7306365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306365).length < 2 ^ (prefixWord ++ tailWord_7306365).sum := by decide
  have hdescent : baseEnd_7306365 < baseStart_7306365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306405 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_7306405 : Nat := 118140960795 + 7306405 * 2 ^ 59
def prefixEnd_7306405 : Nat := 4983230072969 + 3 ^ 40 * 7306405 * 2
def baseEnd_7306405 : Nat := 1250565873804530463511987

theorem tailTrace_7306405 : CollatzResearch.WordTrace tailWord_7306405 prefixEnd_7306405 1250565873804530463511987 := by
  unfold tailWord_7306405
  simp only [CollatzResearch.WordTrace]
  refine ⟨266486483095149994473920669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177657655396766662982613779 266486483095149994473920669)
  ·
    refine ⟨99932431160681247927720251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266486483095149994473920669 99932431160681247927720251)
    ·
      refine ⟨149898646741021871891580377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99932431160681247927720251 149898646741021871891580377)
      ·
        refine ⟨112423985055766403918685283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149898646741021871891580377 112423985055766403918685283)
        ·
          refine ⟨168635977583649605878027925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112423985055766403918685283 168635977583649605878027925)
          ·
            refine ⟨7904811449233575275532559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168635977583649605878027925 7904811449233575275532559)
            ·
              refine ⟨11857217173850362913298839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904811449233575275532559 11857217173850362913298839)
              ·
                refine ⟨17785825760775544369948259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857217173850362913298839 17785825760775544369948259)
                ·
                  refine ⟨26678738641163316554922389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17785825760775544369948259 26678738641163316554922389)
                  ·
                    refine ⟨1250565873804530463511987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26678738641163316554922389 1250565873804530463511987)
                    ·
                      rfl

theorem cell23_7306405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_7306405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306405 prefixEnd_7306405 := by exact prefixLift 7306405
  have htrace : WordTrace (prefixWord ++ tailWord_7306405) baseStart_7306405 baseEnd_7306405 := by
    simpa [prefixWord, tailWord_7306405, baseEnd_7306405] using wordTrace_append hprefix tailTrace_7306405
  have hstable : (prefixWord ++ tailWord_7306405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306405).length < 2 ^ (prefixWord ++ tailWord_7306405).sum := by decide
  have hdescent : baseEnd_7306405 < baseStart_7306405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306411 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_7306411 : Nat := 118140960795 + 7306411 * 2 ^ 59
def prefixEnd_7306411 : Nat := 4983230072969 + 3 ^ 40 * 7306411 * 2
def baseEnd_7306411 : Nat := 3751700702297518367060933

theorem tailTrace_7306411 : CollatzResearch.WordTrace tailWord_7306411 prefixEnd_7306411 3751700702297518367060933 := by
  unfold tailWord_7306411
  simp only [CollatzResearch.WordTrace]
  refine ⟨266486701933128257498639087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177657801288752171665759391 266486701933128257498639087)
  ·
    refine ⟨399730052899692386247958631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266486701933128257498639087 399730052899692386247958631)
    ·
      refine ⟨599595079349538579371937947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399730052899692386247958631 599595079349538579371937947)
      ·
        refine ⟨899392619024307869057906921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599595079349538579371937947 899392619024307869057906921)
        ·
          refine ⟨674544464268230901793430191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899392619024307869057906921 674544464268230901793430191)
          ·
            refine ⟨1011816696402346352690145287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674544464268230901793430191 1011816696402346352690145287)
            ·
              refine ⟨1517725044603519529035217931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011816696402346352690145287 1517725044603519529035217931)
              ·
                refine ⟨2276587566905279293552826897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517725044603519529035217931 2276587566905279293552826897)
                ·
                  refine ⟨1707440675178959470164620173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276587566905279293552826897 1707440675178959470164620173)
                  ·
                    refine ⟨640290253192109801311732565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1707440675178959470164620173 640290253192109801311732565)
                    ·
                      refine ⟨3751700702297518367060933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 640290253192109801311732565 3751700702297518367060933)
                      ·
                        rfl

theorem cell23_7306411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_7306411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306411 prefixEnd_7306411 := by exact prefixLift 7306411
  have htrace : WordTrace (prefixWord ++ tailWord_7306411) baseStart_7306411 baseEnd_7306411 := by
    simpa [prefixWord, tailWord_7306411, baseEnd_7306411] using wordTrace_append hprefix tailTrace_7306411
  have hstable : (prefixWord ++ tailWord_7306411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306411).length < 2 ^ (prefixWord ++ tailWord_7306411).sum := by decide
  have hdescent : baseEnd_7306411 < baseStart_7306411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306415 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_7306415 : Nat := 118140960795 + 7306415 * 2 ^ 59
def prefixEnd_7306415 : Nat := 4983230072969 + 3 ^ 40 * 7306415 * 2
def baseEnd_7306415 : Nat := 3751702756220136351410915

theorem tailTrace_7306415 : CollatzResearch.WordTrace tailWord_7306415 prefixEnd_7306415 3751702756220136351410915 := by
  unfold tailWord_7306415
  simp only [CollatzResearch.WordTrace]
  refine ⟨266486847825113766181784699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177657898550075844121189799 266486847825113766181784699)
  ·
    refine ⟨399730271737670649272677049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266486847825113766181784699 399730271737670649272677049)
    ·
      refine ⟨299797703803252986954507787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399730271737670649272677049 299797703803252986954507787)
      ·
        refine ⟨449696555704879480431761681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299797703803252986954507787 449696555704879480431761681)
        ·
          refine ⟨337272416778659610323821261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449696555704879480431761681 337272416778659610323821261)
          ·
            refine ⟨126477156291997353871432973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337272416778659610323821261 126477156291997353871432973)
            ·
              refine ⟨47428933609499007701787365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126477156291997353871432973 47428933609499007701787365)
              ·
                refine ⟨8892925051781063944085131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47428933609499007701787365 8892925051781063944085131)
                ·
                  refine ⟨13339387577671595916127697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892925051781063944085131 13339387577671595916127697)
                  ·
                    refine ⟨10004540683253696937095773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13339387577671595916127697 10004540683253696937095773)
                    ·
                      refine ⟨3751702756220136351410915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004540683253696937095773 3751702756220136351410915)
                      ·
                        rfl

theorem cell23_7306415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_7306415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306415 prefixEnd_7306415 := by exact prefixLift 7306415
  have htrace : WordTrace (prefixWord ++ tailWord_7306415) baseStart_7306415 baseEnd_7306415 := by
    simpa [prefixWord, tailWord_7306415, baseEnd_7306415] using wordTrace_append hprefix tailTrace_7306415
  have hstable : (prefixWord ++ tailWord_7306415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306415).length < 2 ^ (prefixWord ++ tailWord_7306415).sum := by decide
  have hdescent : baseEnd_7306415 < baseStart_7306415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306418 : List Nat := [3, 2, 1, 1, 1, 5, 1, 9]
def baseStart_7306418 : Nat := 118140960795 + 7306418 * 2 ^ 59
def prefixEnd_7306418 : Nat := 4983230072969 + 3 ^ 40 * 7306418 * 2
def baseEnd_7306418 : Nat := 138952010987485179247163

theorem tailTrace_7306418 : CollatzResearch.WordTrace tailWord_7306418 prefixEnd_7306418 138952010987485179247163 := by
  unfold tailWord_7306418
  simp only [CollatzResearch.WordTrace]
  refine ⟨66621739311025724423535977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177657971496068598462762605 66621739311025724423535977)
  ·
    refine ⟨49966304483269293317651983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66621739311025724423535977 49966304483269293317651983)
    ·
      refine ⟨74949456724903939976477975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49966304483269293317651983 74949456724903939976477975)
      ·
        refine ⟨112424185087355909964716963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74949456724903939976477975 112424185087355909964716963)
        ·
          refine ⟨168636277631033864947075445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112424185087355909964716963 168636277631033864947075445)
          ·
            refine ⟨15809651027909424838788323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168636277631033864947075445 15809651027909424838788323)
            ·
              refine ⟨23714476541864137258182485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15809651027909424838788323 23714476541864137258182485)
              ·
                refine ⟨138952010987485179247163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23714476541864137258182485 138952010987485179247163)
                ·
                  rfl

theorem cell23_7306418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_7306418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306418 prefixEnd_7306418 := by exact prefixLift 7306418
  have htrace : WordTrace (prefixWord ++ tailWord_7306418) baseStart_7306418 baseEnd_7306418 := by
    simpa [prefixWord, tailWord_7306418, baseEnd_7306418] using wordTrace_append hprefix tailTrace_7306418
  have hstable : (prefixWord ++ tailWord_7306418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306418).length < 2 ^ (prefixWord ++ tailWord_7306418).sum := by decide
  have hdescent : baseEnd_7306418 < baseStart_7306418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306446 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_7306446 : Nat := 118140960795 + 7306446 * 2 ^ 59
def prefixEnd_7306446 : Nat := 4983230072969 + 3 ^ 40 * 7306446 * 2
def baseEnd_7306446 : Nat := 3751718674120425730123273

theorem tailTrace_7306446 : CollatzResearch.WordTrace tailWord_7306446 prefixEnd_7306446 3751718674120425730123273 := by
  unfold tailWord_7306446
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310997311000182309520399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177658652325334305650775461 33310997311000182309520399)
  ·
    refine ⟨49966495966500273464280599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33310997311000182309520399 49966495966500273464280599)
    ·
      refine ⟨74949743949750410196420899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49966495966500273464280599 74949743949750410196420899)
      ·
        refine ⟨112424615924625615294631349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74949743949750410196420899 112424615924625615294631349)
        ·
          refine ⟨10539807742933651433871689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112424615924625615294631349 10539807742933651433871689)
          ·
            refine ⟨7904855807200238575403767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10539807742933651433871689 7904855807200238575403767)
            ·
              refine ⟨11857283710800357863105651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904855807200238575403767 11857283710800357863105651)
              ·
                refine ⟨17785925566200536794658477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857283710800357863105651 17785925566200536794658477)
                ·
                  refine ⟨6669722087325201297996929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17785925566200536794658477 6669722087325201297996929)
                  ·
                    refine ⟨5002291565493900973497697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6669722087325201297996929 5002291565493900973497697)
                    ·
                      refine ⟨3751718674120425730123273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002291565493900973497697 3751718674120425730123273)
                      ·
                        rfl

theorem cell23_7306446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_7306446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306446 prefixEnd_7306446 := by exact prefixLift 7306446
  have htrace : WordTrace (prefixWord ++ tailWord_7306446) baseStart_7306446 baseEnd_7306446 := by
    simpa [prefixWord, tailWord_7306446, baseEnd_7306446] using wordTrace_append hprefix tailTrace_7306446
  have hstable : (prefixWord ++ tailWord_7306446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306446).length < 2 ^ (prefixWord ++ tailWord_7306446).sum := by decide
  have hdescent : baseEnd_7306446 < baseStart_7306446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306452 : List Nat := [2, 4, 1, 4, 1, 1, 2, 8]
def baseStart_7306452 : Nat := 118140960795 + 7306452 * 2 ^ 59
def prefixEnd_7306452 : Nat := 4983230072969 + 3 ^ 40 * 7306452 * 2
def baseEnd_7306452 : Nat := 138952657592753803949935

theorem tailTrace_7306452 : CollatzResearch.WordTrace tailWord_7306452 prefixEnd_7306452 138952657592753803949935 := by
  unfold tailWord_7306452
  simp only [CollatzResearch.WordTrace]
  refine ⟨133244098662989860750440805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177658798217319814333921073 133244098662989860750440805)
  ·
    refine ⟨24983268499310598890707651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133244098662989860750440805 24983268499310598890707651)
    ·
      refine ⟨37474902748965898336061477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24983268499310598890707651 37474902748965898336061477)
      ·
        refine ⟨7026544265431105938011527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37474902748965898336061477 7026544265431105938011527)
        ·
          refine ⟨10539816398146658907017291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026544265431105938011527 10539816398146658907017291)
          ·
            refine ⟨15809724597219988360525937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10539816398146658907017291 15809724597219988360525937)
            ·
              refine ⟨11857293447914991270394453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15809724597219988360525937 11857293447914991270394453)
              ·
                refine ⟨138952657592753803949935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11857293447914991270394453 138952657592753803949935)
                ·
                  rfl

theorem cell23_7306452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 8].length) (baseStart_7306452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306452 prefixEnd_7306452 := by exact prefixLift 7306452
  have htrace : WordTrace (prefixWord ++ tailWord_7306452) baseStart_7306452 baseEnd_7306452 := by
    simpa [prefixWord, tailWord_7306452, baseEnd_7306452] using wordTrace_append hprefix tailTrace_7306452
  have hstable : (prefixWord ++ tailWord_7306452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306452).length < 2 ^ (prefixWord ++ tailWord_7306452).sum := by decide
  have hdescent : baseEnd_7306452 < baseStart_7306452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306456 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_7306456 : Nat := 118140960795 + 7306456 * 2 ^ 59
def prefixEnd_7306456 : Nat := 4983230072969 + 3 ^ 40 * 7306456 * 2
def baseEnd_7306456 : Nat := 1250574602975656896999409

theorem tailTrace_7306456 : CollatzResearch.WordTrace tailWord_7306456 prefixEnd_7306456 1250574602975656896999409 := by
  unfold tailWord_7306456
  simp only [CollatzResearch.WordTrace]
  refine ⟨133244171608982615092013611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177658895478643486789351481 133244171608982615092013611)
  ·
    refine ⟨199866257413473922638020417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133244171608982615092013611 199866257413473922638020417)
    ·
      refine ⟨149899693060105441978515313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199866257413473922638020417 149899693060105441978515313)
      ·
        refine ⟨112424769795079081483886485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149899693060105441978515313 112424769795079081483886485)
        ·
          refine ⟨5269911084144331944557179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112424769795079081483886485 5269911084144331944557179)
          ·
            refine ⟨7904866626216497916835769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269911084144331944557179 7904866626216497916835769)
            ·
              refine ⟨5928649969662373437626827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904866626216497916835769 5928649969662373437626827)
              ·
                refine ⟨8892974954493560156440241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928649969662373437626827 8892974954493560156440241)
                ·
                  refine ⟨6669731215870170117330181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8892974954493560156440241 6669731215870170117330181)
                  ·
                    refine ⟨1250574602975656896999409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669731215870170117330181 1250574602975656896999409)
                    ·
                      rfl

theorem cell23_7306456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_7306456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306456 prefixEnd_7306456 := by exact prefixLift 7306456
  have htrace : WordTrace (prefixWord ++ tailWord_7306456) baseStart_7306456 baseEnd_7306456 := by
    simpa [prefixWord, tailWord_7306456, baseEnd_7306456] using wordTrace_append hprefix tailTrace_7306456
  have hstable : (prefixWord ++ tailWord_7306456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306456).length < 2 ^ (prefixWord ++ tailWord_7306456).sum := by decide
  have hdescent : baseEnd_7306456 < baseStart_7306456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306472 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7306472 : Nat := 118140960795 + 7306472 * 2 ^ 59
def prefixEnd_7306472 : Nat := 4983230072969 + 3 ^ 40 * 7306472 * 2
def baseEnd_7306472 : Nat := 3751732024617442628398153

theorem tailTrace_7306472 : CollatzResearch.WordTrace tailWord_7306472 prefixEnd_7306472 3751732024617442628398153 := by
  unfold tailWord_7306472
  simp only [CollatzResearch.WordTrace]
  refine ⟨133244463392953632458304835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177659284523938176611073113 133244463392953632458304835)
  ·
    refine ⟨199866695089430448687457253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133244463392953632458304835 199866695089430448687457253)
    ·
      refine ⟨37475005329268209128898235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199866695089430448687457253 37475005329268209128898235)
      ·
        refine ⟨56212507993902313693347353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37475005329268209128898235 56212507993902313693347353)
        ·
          refine ⟨42159380995426735270010515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56212507993902313693347353 42159380995426735270010515)
          ·
            refine ⟨63239071493140102905015773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42159380995426735270010515 63239071493140102905015773)
            ·
              refine ⟨23714651809927538589380915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63239071493140102905015773 23714651809927538589380915)
              ·
                refine ⟨35571977714891307884071373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23714651809927538589380915 35571977714891307884071373)
                ·
                  refine ⟨13339491643084240456526765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35571977714891307884071373 13339491643084240456526765)
                  ·
                    refine ⟨5002309366156590171197537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13339491643084240456526765 5002309366156590171197537)
                    ·
                      refine ⟨3751732024617442628398153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002309366156590171197537 3751732024617442628398153)
                      ·
                        rfl

theorem cell23_7306472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7306472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306472 prefixEnd_7306472 := by exact prefixLift 7306472
  have htrace : WordTrace (prefixWord ++ tailWord_7306472) baseStart_7306472 baseEnd_7306472 := by
    simpa [prefixWord, tailWord_7306472, baseEnd_7306472] using wordTrace_append hprefix tailTrace_7306472
  have hstable : (prefixWord ++ tailWord_7306472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306472).length < 2 ^ (prefixWord ++ tailWord_7306472).sum := by decide
  have hdescent : baseEnd_7306472 < baseStart_7306472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306489 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 1, 3, 2]
def baseStart_7306489 : Nat := 118140960795 + 7306489 * 2 ^ 59
def prefixEnd_7306489 : Nat := 4983230072969 + 3 ^ 40 * 7306489 * 2
def baseEnd_7306489 : Nat := 3751740753788569061885575

theorem tailTrace_7306489 : CollatzResearch.WordTrace tailWord_7306489 prefixEnd_7306489 3751740753788569061885575 := by
  unfold tailWord_7306489
  simp only [CollatzResearch.WordTrace]
  refine ⟨266489546826845676819978521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177659697884563784546652347 266489546826845676819978521)
  ·
    refine ⟨199867160120134257614983891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266489546826845676819978521 199867160120134257614983891)
    ·
      refine ⟨299800740180201386422475837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199867160120134257614983891 299800740180201386422475837)
      ·
        refine ⟨112425277567575519908428439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299800740180201386422475837 112425277567575519908428439)
        ·
          refine ⟨168637916351363279862642659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112425277567575519908428439 168637916351363279862642659)
          ·
            refine ⟨252956874527044919793963989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168637916351363279862642659 252956874527044919793963989)
            ·
              refine ⟨5928676746727615307671031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252956874527044919793963989 5928676746727615307671031)
              ·
                refine ⟨8893015120091422961506547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928676746727615307671031 8893015120091422961506547)
                ·
                  refine ⟨13339522680137134442259821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893015120091422961506547 13339522680137134442259821)
                  ·
                    refine ⟨5002321005051425415847433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13339522680137134442259821 5002321005051425415847433)
                    ·
                      refine ⟨3751740753788569061885575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002321005051425415847433 3751740753788569061885575)
                      ·
                        rfl

theorem cell23_7306489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_7306489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306489 prefixEnd_7306489 := by exact prefixLift 7306489
  have htrace : WordTrace (prefixWord ++ tailWord_7306489) baseStart_7306489 baseEnd_7306489 := by
    simpa [prefixWord, tailWord_7306489, baseEnd_7306489] using wordTrace_append hprefix tailTrace_7306489
  have hstable : (prefixWord ++ tailWord_7306489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306489).length < 2 ^ (prefixWord ++ tailWord_7306489).sum := by decide
  have hdescent : baseEnd_7306489 < baseStart_7306489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306519 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7306519 : Nat := 118140960795 + 7306519 * 2 ^ 59
def prefixEnd_7306519 : Nat := 4983230072969 + 3 ^ 40 * 7306519 * 2
def baseEnd_7306519 : Nat := 3751756158208203944510437

theorem tailTrace_7306519 : CollatzResearch.WordTrace tailWord_7306519 prefixEnd_7306519 3751756158208203944510437 := by
  unfold tailWord_7306519
  simp only [CollatzResearch.WordTrace]
  refine ⟨266490641016736991943570611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177660427344491327962380407 266490641016736991943570611)
  ·
    refine ⟨399735961525105487915355917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266490641016736991943570611 399735961525105487915355917)
    ·
      refine ⟨149900985571914557968258469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399735961525105487915355917 149900985571914557968258469)
      ·
        refine ⟨28106434794733979619048463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149900985571914557968258469 28106434794733979619048463)
        ·
          refine ⟨42159652192100969428572695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28106434794733979619048463 42159652192100969428572695)
          ·
            refine ⟨63239478288151454142859043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42159652192100969428572695 63239478288151454142859043)
            ·
              refine ⟨94859217432227181214288565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63239478288151454142859043 94859217432227181214288565)
              ·
                refine ⟨8893051634271298238839553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94859217432227181214288565 8893051634271298238839553)
                ·
                  refine ⟨6669788725703473679129665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893051634271298238839553 6669788725703473679129665)
                  ·
                    refine ⟨5002341544277605259347249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6669788725703473679129665 5002341544277605259347249)
                    ·
                      refine ⟨3751756158208203944510437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002341544277605259347249 3751756158208203944510437)
                      ·
                        rfl

theorem cell23_7306519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7306519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306519 prefixEnd_7306519 := by exact prefixLift 7306519
  have htrace : WordTrace (prefixWord ++ tailWord_7306519) baseStart_7306519 baseEnd_7306519 := by
    simpa [prefixWord, tailWord_7306519, baseEnd_7306519] using wordTrace_append hprefix tailTrace_7306519
  have hstable : (prefixWord ++ tailWord_7306519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306519).length < 2 ^ (prefixWord ++ tailWord_7306519).sum := by decide
  have hdescent : baseEnd_7306519 < baseStart_7306519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306525 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 9]
def baseStart_7306525 : Nat := 118140960795 + 7306525 * 2 ^ 59
def prefixEnd_7306525 : Nat := 4983230072969 + 3 ^ 40 * 7306525 * 2
def baseEnd_7306525 : Nat := 416862137676903435670601

theorem tailTrace_7306525 : CollatzResearch.WordTrace tailWord_7306525 prefixEnd_7306525 416862137676903435670601 := by
  unfold tailWord_7306525
  simp only [CollatzResearch.WordTrace]
  refine ⟨266490859854715254968289029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177660573236476836645526019 266490859854715254968289029)
  ·
    refine ⟨49967036222759110306554193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266490859854715254968289029 49967036222759110306554193)
    ·
      refine ⟨37475277167069332729915645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49967036222759110306554193 37475277167069332729915645)
      ·
        refine ⟨14053228937650999773718367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37475277167069332729915645 14053228937650999773718367)
        ·
          refine ⟨21079843406476499660577551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14053228937650999773718367 21079843406476499660577551)
          ·
            refine ⟨31619765109714749490866327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21079843406476499660577551 31619765109714749490866327)
            ·
              refine ⟨47429647664572124236299491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31619765109714749490866327 47429647664572124236299491)
              ·
                refine ⟨71144471496858186354449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47429647664572124236299491 71144471496858186354449237)
                ·
                  refine ⟨416862137676903435670601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71144471496858186354449237 416862137676903435670601)
                  ·
                    rfl

theorem cell23_7306525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_7306525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306525 prefixEnd_7306525 := by exact prefixLift 7306525
  have htrace : WordTrace (prefixWord ++ tailWord_7306525) baseStart_7306525 baseEnd_7306525 := by
    simpa [prefixWord, tailWord_7306525, baseEnd_7306525] using wordTrace_append hprefix tailTrace_7306525
  have hstable : (prefixWord ++ tailWord_7306525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306525).length < 2 ^ (prefixWord ++ tailWord_7306525).sum := by decide
  have hdescent : baseEnd_7306525 < baseStart_7306525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306553 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7306553 : Nat := 118140960795 + 7306553 * 2 ^ 59
def prefixEnd_7306553 : Nat := 4983230072969 + 3 ^ 40 * 7306553 * 2
def baseEnd_7306553 : Nat := 3751773616550456811485281

theorem tailTrace_7306553 : CollatzResearch.WordTrace tailWord_7306553 prefixEnd_7306553 3751773616550456811485281 := by
  unfold tailWord_7306553
  simp only [CollatzResearch.WordTrace]
  refine ⟨266491881098613815750308313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177661254065742543833538875 266491881098613815750308313)
  ·
    refine ⟨199868910823960361812731235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266491881098613815750308313 199868910823960361812731235)
    ·
      refine ⟨299803366235940542719096853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199868910823960361812731235 299803366235940542719096853)
      ·
        refine ⟨14053282792309712939957665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299803366235940542719096853 14053282792309712939957665)
        ·
          refine ⟨10539962094232284704968249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14053282792309712939957665 10539962094232284704968249)
          ·
            refine ⟨7904971570674213528726187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10539962094232284704968249 7904971570674213528726187)
            ·
              refine ⟨11857457356011320293089281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904971570674213528726187 11857457356011320293089281)
              ·
                refine ⟨8893093017008490219816961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857457356011320293089281 8893093017008490219816961)
                ·
                  refine ⟨6669819762756367664862721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893093017008490219816961 6669819762756367664862721)
                  ·
                    refine ⟨5002364822067275748647041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6669819762756367664862721 5002364822067275748647041)
                    ·
                      refine ⟨3751773616550456811485281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002364822067275748647041 3751773616550456811485281)
                      ·
                        rfl

theorem cell23_7306553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7306553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306553 prefixEnd_7306553 := by exact prefixLift 7306553
  have htrace : WordTrace (prefixWord ++ tailWord_7306553) baseStart_7306553 baseEnd_7306553 := by
    simpa [prefixWord, tailWord_7306553, baseEnd_7306553] using wordTrace_append hprefix tailTrace_7306553
  have hstable : (prefixWord ++ tailWord_7306553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306553).length < 2 ^ (prefixWord ++ tailWord_7306553).sum := by decide
  have hdescent : baseEnd_7306553 < baseStart_7306553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306615 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 6]
def baseStart_7306615 : Nat := 118140960795 + 7306615 * 2 ^ 59
def prefixEnd_7306615 : Nat := 4983230072969 + 3 ^ 40 * 7306615 * 2
def baseEnd_7306615 : Nat := 416867272483448396545555

theorem tailTrace_7306615 : CollatzResearch.WordTrace tailWord_7306615 prefixEnd_7306615 416867272483448396545555 := by
  unfold tailWord_7306615
  simp only [CollatzResearch.WordTrace]
  refine ⟨266494142424389200339065299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177662761616259466892710199 266494142424389200339065299)
  ·
    refine ⟨399741213636583800508597949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266494142424389200339065299 399741213636583800508597949)
    ·
      refine ⟨149902955113718925190724231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399741213636583800508597949 149902955113718925190724231)
      ·
        refine ⟨224854432670578387786086347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149902955113718925190724231 224854432670578387786086347)
        ·
          refine ⟨337281649005867581679129521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224854432670578387786086347 337281649005867581679129521)
          ·
            refine ⟨252961236754400686259347141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337281649005867581679129521 252961236754400686259347141)
            ·
              refine ⟨47430231891450128673627589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252961236754400686259347141 47430231891450128673627589)
              ·
                refine ⟨8893168479646899126305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47430231891450128673627589 8893168479646899126305173)
                ·
                  refine ⟨416867272483448396545555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8893168479646899126305173 416867272483448396545555)
                  ·
                    rfl

theorem cell23_7306615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 6].length) (baseStart_7306615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306615 prefixEnd_7306615 := by exact prefixLift 7306615
  have htrace : WordTrace (prefixWord ++ tailWord_7306615) baseStart_7306615 baseEnd_7306615 := by
    simpa [prefixWord, tailWord_7306615, baseEnd_7306615] using wordTrace_append hprefix tailTrace_7306615
  have hstable : (prefixWord ++ tailWord_7306615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306615).length < 2 ^ (prefixWord ++ tailWord_7306615).sum := by decide
  have hdescent : baseEnd_7306615 < baseStart_7306615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306632 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 6]
def baseStart_7306632 : Nat := 118140960795 + 7306632 * 2 ^ 59
def prefixEnd_7306632 : Nat := 4983230072969 + 3 ^ 40 * 7306632 * 2
def baseEnd_7306632 : Nat := 416868242391351333599713

theorem tailTrace_7306632 : CollatzResearch.WordTrace tailWord_7306632 prefixEnd_7306632 416868242391351333599713 := by
  unfold tailWord_7306632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133247381232663806121217075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177663174976885074828289433 133247381232663806121217075)
  ·
    refine ⟨199871071848995709181825613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133247381232663806121217075 199871071848995709181825613)
    ·
      refine ⟨74951651943373390943184605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199871071848995709181825613 74951651943373390943184605)
      ·
        refine ⟨28106869478765021603694227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74951651943373390943184605 28106869478765021603694227)
        ·
          refine ⟨42160304218147532405541341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28106869478765021603694227 42160304218147532405541341)
          ·
            refine ⟨15810114081805324652078003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42160304218147532405541341 15810114081805324652078003)
            ·
              refine ⟨23715171122707986978117005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15810114081805324652078003 23715171122707986978117005)
              ·
                refine ⟨8893189171015495116793877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23715171122707986978117005 8893189171015495116793877)
                ·
                  refine ⟨416868242391351333599713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8893189171015495116793877 416868242391351333599713)
                  ·
                    rfl

theorem cell23_7306632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_7306632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306632 prefixEnd_7306632 := by exact prefixLift 7306632
  have htrace : WordTrace (prefixWord ++ tailWord_7306632) baseStart_7306632 baseEnd_7306632 := by
    simpa [prefixWord, tailWord_7306632, baseEnd_7306632] using wordTrace_append hprefix tailTrace_7306632
  have hstable : (prefixWord ++ tailWord_7306632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306632).length < 2 ^ (prefixWord ++ tailWord_7306632).sum := by decide
  have hdescent : baseEnd_7306632 < baseStart_7306632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306682 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_7306682 : Nat := 118140960795 + 7306682 * 2 ^ 59
def prefixEnd_7306682 : Nat := 4983230072969 + 3 ^ 40 * 7306682 * 2
def baseEnd_7306682 : Nat := 3751839855554886806772187

theorem tailTrace_7306682 : CollatzResearch.WordTrace tailWord_7306682 prefixEnd_7306682 3751839855554886806772187 := by
  unfold tailWord_7306682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66624146528786617695438575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177664390743430980521169533 66624146528786617695438575)
  ·
    refine ⟨99936219793179926543157863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66624146528786617695438575 99936219793179926543157863)
    ·
      refine ⟨149904329689769889814736795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99936219793179926543157863 149904329689769889814736795)
      ·
        refine ⟨224856494534654834722105193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149904329689769889814736795 224856494534654834722105193)
        ·
          refine ⟨168642370900991126041578895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224856494534654834722105193 168642370900991126041578895)
          ·
            refine ⟨252963556351486689062368343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168642370900991126041578895 252963556351486689062368343)
            ·
              refine ⟨379445334527230033593552515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252963556351486689062368343 379445334527230033593552515)
              ·
                refine ⟨569168001790845050390328773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379445334527230033593552515 569168001790845050390328773)
                ·
                  refine ⟨106719000335783446948186645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569168001790845050390328773 106719000335783446948186645)
                  ·
                    refine ⟨5002453140739849075696249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106719000335783446948186645 5002453140739849075696249)
                    ·
                      refine ⟨3751839855554886806772187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002453140739849075696249 3751839855554886806772187)
                      ·
                        rfl

theorem cell23_7306682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_7306682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306682 prefixEnd_7306682 := by exact prefixLift 7306682
  have htrace : WordTrace (prefixWord ++ tailWord_7306682) baseStart_7306682 baseEnd_7306682 := by
    simpa [prefixWord, tailWord_7306682, baseEnd_7306682] using wordTrace_append hprefix tailTrace_7306682
  have hstable : (prefixWord ++ tailWord_7306682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306682).length < 2 ^ (prefixWord ++ tailWord_7306682).sum := by decide
  have hdescent : baseEnd_7306682 < baseStart_7306682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306699 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 5, 2, 2]
def baseStart_7306699 : Nat := 118140960795 + 7306699 * 2 ^ 59
def prefixEnd_7306699 : Nat := 4983230072969 + 3 ^ 40 * 7306699 * 2
def baseEnd_7306699 : Nat := 3751848584726013240259609

theorem tailTrace_7306699 : CollatzResearch.WordTrace tailWord_7306699 prefixEnd_7306699 3751848584726013240259609 := by
  unfold tailWord_7306699
  simp only [CollatzResearch.WordTrace]
  refine ⟨266497206156084882685123151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177664804104056588456748767 266497206156084882685123151)
  ·
    refine ⟨399745809234127324027684727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266497206156084882685123151 399745809234127324027684727)
    ·
      refine ⟨599618713851190986041527091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399745809234127324027684727 599618713851190986041527091)
      ·
        refine ⟨899428070776786479062290637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599618713851190986041527091 899428070776786479062290637)
        ·
          refine ⟨337285526541294929648358989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899428070776786479062290637 337285526541294929648358989)
          ·
            refine ⟨126482072452985598618134621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337285526541294929648358989 126482072452985598618134621)
            ·
              refine ⟨47430777169869599481800483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126482072452985598618134621 47430777169869599481800483)
              ·
                refine ⟨71146165754804399222700725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47430777169869599481800483 71146165754804399222700725)
                ·
                  refine ⟨6669953039512912427128193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71146165754804399222700725 6669953039512912427128193)
                  ·
                    refine ⟨5002464779634684320346145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6669953039512912427128193 5002464779634684320346145)
                    ·
                      refine ⟨3751848584726013240259609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002464779634684320346145 3751848584726013240259609)
                      ·
                        rfl

theorem cell23_7306699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2, 2].length) (baseStart_7306699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306699 prefixEnd_7306699 := by exact prefixLift 7306699
  have htrace : WordTrace (prefixWord ++ tailWord_7306699) baseStart_7306699 baseEnd_7306699 := by
    simpa [prefixWord, tailWord_7306699, baseEnd_7306699] using wordTrace_append hprefix tailTrace_7306699
  have hstable : (prefixWord ++ tailWord_7306699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306699).length < 2 ^ (prefixWord ++ tailWord_7306699).sum := by decide
  have hdescent : baseEnd_7306699 < baseStart_7306699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306710 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7306710 : Nat := 118140960795 + 7306710 * 2 ^ 59
def prefixEnd_7306710 : Nat := 4983230072969 + 3 ^ 40 * 7306710 * 2
def baseEnd_7306710 : Nat := 3751854233013212697222059

theorem tailTrace_7306710 : CollatzResearch.WordTrace tailWord_7306710 prefixEnd_7306710 3751854233013212697222059 := by
  unfold tailWord_7306710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656100459940314472735849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177665071572696687709182389 16656100459940314472735849)
  ·
    refine ⟨12492075344955235854551887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16656100459940314472735849 12492075344955235854551887)
    ·
      refine ⟨18738113017432853781827831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12492075344955235854551887 18738113017432853781827831)
      ·
        refine ⟨28107169526149280672741747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18738113017432853781827831 28107169526149280672741747)
        ·
          refine ⟨42160754289223921009112621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28107169526149280672741747 42160754289223921009112621)
          ·
            refine ⟨15810282858458970378417233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42160754289223921009112621 15810282858458970378417233)
            ·
              refine ⟨11857712143844227783812925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15810282858458970378417233 11857712143844227783812925)
              ·
                refine ⟨4446642053941585418929847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11857712143844227783812925 4446642053941585418929847)
                ·
                  refine ⟨6669963080912378128394771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446642053941585418929847 6669963080912378128394771)
                  ·
                    refine ⟨10004944621368567192592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669963080912378128394771 10004944621368567192592157)
                    ·
                      refine ⟨3751854233013212697222059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004944621368567192592157 3751854233013212697222059)
                      ·
                        rfl

theorem cell23_7306710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7306710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306710 prefixEnd_7306710 := by exact prefixLift 7306710
  have htrace : WordTrace (prefixWord ++ tailWord_7306710) baseStart_7306710 baseEnd_7306710 := by
    simpa [prefixWord, tailWord_7306710, baseEnd_7306710] using wordTrace_append hprefix tailTrace_7306710
  have hstable : (prefixWord ++ tailWord_7306710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306710).length < 2 ^ (prefixWord ++ tailWord_7306710).sum := by decide
  have hdescent : baseEnd_7306710 < baseStart_7306710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306712 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7306712 : Nat := 118140960795 + 7306712 * 2 ^ 59
def prefixEnd_7306712 : Nat := 4983230072969 + 3 ^ 40 * 7306712 * 2
def baseEnd_7306712 : Nat := 3751855259974521689397049

theorem tailTrace_7306712 : CollatzResearch.WordTrace tailWord_7306712 prefixEnd_7306712 3751855259974521689397049 := by
  unfold tailWord_7306712
  simp only [CollatzResearch.WordTrace]
  refine ⟨133248840152518892952673195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177665120203358523936897593 133248840152518892952673195)
  ·
    refine ⟨199873260228778339429009793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133248840152518892952673195 199873260228778339429009793)
    ·
      refine ⟨149904945171583754571757345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199873260228778339429009793 149904945171583754571757345)
      ·
        refine ⟨112428708878687815928818009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149904945171583754571757345 112428708878687815928818009)
        ·
          refine ⟨84321531659015861946613507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112428708878687815928818009 84321531659015861946613507)
          ·
            refine ⟨126482297488523792919920261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84321531659015861946613507 126482297488523792919920261)
            ·
              refine ⟨23715430779098211172485049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126482297488523792919920261 23715430779098211172485049)
              ·
                refine ⟨17786573084323658379363787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23715430779098211172485049 17786573084323658379363787)
                ·
                  refine ⟨26679859626485487569045681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17786573084323658379363787 26679859626485487569045681)
                  ·
                    refine ⟨20009894719864115676784261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26679859626485487569045681 20009894719864115676784261)
                    ·
                      refine ⟨3751855259974521689397049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20009894719864115676784261 3751855259974521689397049)
                      ·
                        rfl

theorem cell23_7306712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7306712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306712 prefixEnd_7306712 := by exact prefixLift 7306712
  have htrace : WordTrace (prefixWord ++ tailWord_7306712) baseStart_7306712 baseEnd_7306712 := by
    simpa [prefixWord, tailWord_7306712, baseEnd_7306712] using wordTrace_append hprefix tailTrace_7306712
  have hstable : (prefixWord ++ tailWord_7306712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306712).length < 2 ^ (prefixWord ++ tailWord_7306712).sum := by decide
  have hdescent : baseEnd_7306712 < baseStart_7306712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306719 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_7306719 : Nat := 118140960795 + 7306719 * 2 ^ 59
def prefixEnd_7306719 : Nat := 4983230072969 + 3 ^ 40 * 7306719 * 2
def baseEnd_7306719 : Nat := 3751858854339103162009517

theorem tailTrace_7306719 : CollatzResearch.WordTrace tailWord_7306719 prefixEnd_7306719 3751858854339103162009517 := by
  unfold tailWord_7306719
  simp only [CollatzResearch.WordTrace]
  refine ⟨266497935616012426100851211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177665290410674950733900807 266497935616012426100851211)
  ·
    refine ⟨399746903424018639151276817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266497935616012426100851211 399746903424018639151276817)
    ·
      refine ⟨299810177568013979363457613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399746903424018639151276817 299810177568013979363457613)
      ·
        refine ⟨112428816588005242261296605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299810177568013979363457613 112428816588005242261296605)
        ·
          refine ⟨42160806220501965847986227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112428816588005242261296605 42160806220501965847986227)
          ·
            refine ⟨63241209330752948771979341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42160806220501965847986227 63241209330752948771979341)
            ·
              refine ⟨23715453499032355789492253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63241209330752948771979341 23715453499032355789492253)
              ·
                refine ⟨8893295062137133421059595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23715453499032355789492253 8893295062137133421059595)
                ·
                  refine ⟨13339942593205700131589393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893295062137133421059595 13339942593205700131589393)
                  ·
                    refine ⟨10004956944904275098692045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13339942593205700131589393 10004956944904275098692045)
                    ·
                      refine ⟨3751858854339103162009517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004956944904275098692045 3751858854339103162009517)
                      ·
                        rfl

theorem cell23_7306719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_7306719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306719 prefixEnd_7306719 := by exact prefixLift 7306719
  have htrace : WordTrace (prefixWord ++ tailWord_7306719) baseStart_7306719 baseEnd_7306719 := by
    simpa [prefixWord, tailWord_7306719, baseEnd_7306719] using wordTrace_append hprefix tailTrace_7306719
  have hstable : (prefixWord ++ tailWord_7306719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306719).length < 2 ^ (prefixWord ++ tailWord_7306719).sum := by decide
  have hdescent : baseEnd_7306719 < baseStart_7306719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306735 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 9]
def baseStart_7306735 : Nat := 118140960795 + 7306735 * 2 ^ 59
def prefixEnd_7306735 : Nat := 4983230072969 + 3 ^ 40 * 7306735 * 2
def baseEnd_7306735 : Nat := 1250622356676525033136481

theorem tailTrace_7306735 : CollatzResearch.WordTrace tailWord_7306735 prefixEnd_7306735 1250622356676525033136481 := by
  unfold tailWord_7306735
  simp only [CollatzResearch.WordTrace]
  refine ⟨266498519183954460833433659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177665679455969640555622439 266498519183954460833433659)
  ·
    refine ⟨399747778775931691250150489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266498519183954460833433659 399747778775931691250150489)
    ·
      refine ⟨299810834081948768437612867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399747778775931691250150489 299810834081948768437612867)
      ·
        refine ⟨449716251122923152656419301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299810834081948768437612867 449716251122923152656419301)
        ·
          refine ⟨84321797085548091123078619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449716251122923152656419301 84321797085548091123078619)
          ·
            refine ⟨126482695628322136684617929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84321797085548091123078619 126482695628322136684617929)
            ·
              refine ⟨94862021721241602513463447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126482695628322136684617929 94862021721241602513463447)
              ·
                refine ⟨142293032581862403770195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94862021721241602513463447 142293032581862403770195171)
                ·
                  refine ⟨213439548872793605655292757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142293032581862403770195171 213439548872793605655292757)
                  ·
                    refine ⟨1250622356676525033136481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 213439548872793605655292757 1250622356676525033136481)
                    ·
                      rfl

theorem cell23_7306735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_7306735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306735 prefixEnd_7306735 := by exact prefixLift 7306735
  have htrace : WordTrace (prefixWord ++ tailWord_7306735) baseStart_7306735 baseEnd_7306735 := by
    simpa [prefixWord, tailWord_7306735, baseEnd_7306735] using wordTrace_append hprefix tailTrace_7306735
  have hstable : (prefixWord ++ tailWord_7306735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306735).length < 2 ^ (prefixWord ++ tailWord_7306735).sum := by decide
  have hdescent : baseEnd_7306735 < baseStart_7306735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306749 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_7306749 : Nat := 118140960795 + 7306749 * 2 ^ 59
def prefixEnd_7306749 : Nat := 4983230072969 + 3 ^ 40 * 7306749 * 2
def baseEnd_7306749 : Nat := 3751874258758738044634379

theorem tailTrace_7306749 : CollatzResearch.WordTrace tailWord_7306749 prefixEnd_7306749 3751874258758738044634379 := by
  unfold tailWord_7306749
  simp only [CollatzResearch.WordTrace]
  refine ⟨266499029805903741224443301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177666019870602494149628867 266499029805903741224443301)
  ·
    refine ⟨49968568088606951479583119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266499029805903741224443301 49968568088606951479583119)
    ·
      refine ⟨74952852132910427219374679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49968568088606951479583119 74952852132910427219374679)
      ·
        refine ⟨112429278199365640829062019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74952852132910427219374679 112429278199365640829062019)
        ·
          refine ⟨168643917299048461243593029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112429278199365640829062019 168643917299048461243593029)
          ·
            refine ⟨31620734493571586483173693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168643917299048461243593029 31620734493571586483173693)
            ·
              refine ⟨11857775435089344931190135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31620734493571586483173693 11857775435089344931190135)
              ·
                refine ⟨17786663152634017396785203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857775435089344931190135 17786663152634017396785203)
                ·
                  refine ⟨26679994728951026095177805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17786663152634017396785203 26679994728951026095177805)
                  ·
                    refine ⟨10004998023356634785691677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26679994728951026095177805 10004998023356634785691677)
                    ·
                      refine ⟨3751874258758738044634379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10004998023356634785691677 3751874258758738044634379)
                      ·
                        rfl

theorem cell23_7306749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_7306749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306749 prefixEnd_7306749 := by exact prefixLift 7306749
  have htrace : WordTrace (prefixWord ++ tailWord_7306749) baseStart_7306749 baseEnd_7306749 := by
    simpa [prefixWord, tailWord_7306749, baseEnd_7306749] using wordTrace_append hprefix tailTrace_7306749
  have hstable : (prefixWord ++ tailWord_7306749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306749).length < 2 ^ (prefixWord ++ tailWord_7306749).sum := by decide
  have hdescent : baseEnd_7306749 < baseStart_7306749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306755 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_7306755 : Nat := 118140960795 + 7306755 * 2 ^ 59
def prefixEnd_7306755 : Nat := 4983230072969 + 3 ^ 40 * 7306755 * 2
def baseEnd_7306755 : Nat := 3751877339642665021159351

theorem tailTrace_7306755 : CollatzResearch.WordTrace tailWord_7306755 prefixEnd_7306755 3751877339642665021159351 := by
  unfold tailWord_7306755
  simp only [CollatzResearch.WordTrace]
  refine ⟨266499248643882004249161719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177666165762588002832774479 266499248643882004249161719)
  ·
    refine ⟨399748872965823006373742579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266499248643882004249161719 399748872965823006373742579)
    ·
      refine ⟨599623309448734509560613869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399748872965823006373742579 599623309448734509560613869)
      ·
        refine ⟨224858741043275441085230201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 599623309448734509560613869 224858741043275441085230201)
        ·
          refine ⟨168644055782456580813922651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224858741043275441085230201 168644055782456580813922651)
          ·
            refine ⟨252966083673684871220883977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168644055782456580813922651 252966083673684871220883977)
            ·
              refine ⟨189724562755263653415662983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252966083673684871220883977 189724562755263653415662983)
              ·
                refine ⟨284586844132895480123494475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189724562755263653415662983 284586844132895480123494475)
                ·
                  refine ⟨426880266199343220185241713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284586844132895480123494475 426880266199343220185241713)
                  ·
                    refine ⟨320160199649507415138931285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 426880266199343220185241713 320160199649507415138931285)
                    ·
                      refine ⟨3751877339642665021159351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320160199649507415138931285 3751877339642665021159351)
                      ·
                        rfl

theorem cell23_7306755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_7306755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306755 prefixEnd_7306755 := by exact prefixLift 7306755
  have htrace : WordTrace (prefixWord ++ tailWord_7306755) baseStart_7306755 baseEnd_7306755 := by
    simpa [prefixWord, tailWord_7306755, baseEnd_7306755] using wordTrace_append hprefix tailTrace_7306755
  have hstable : (prefixWord ++ tailWord_7306755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306755).length < 2 ^ (prefixWord ++ tailWord_7306755).sum := by decide
  have hdescent : baseEnd_7306755 < baseStart_7306755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306756 : List Nat := [2, 3, 2, 3, 2, 2, 2, 7]
def baseStart_7306756 : Nat := 118140960795 + 7306756 * 2 ^ 59
def prefixEnd_7306756 : Nat := 4983230072969 + 3 ^ 40 * 7306756 * 2
def baseEnd_7306756 : Nat := 138958439004567389527661

theorem tailTrace_7306756 : CollatzResearch.WordTrace tailWord_7306756 prefixEnd_7306756 138958439004567389527661 := by
  unfold tailWord_7306756
  simp only [CollatzResearch.WordTrace]
  refine ⟨133249642558439190709974061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177666190077918920946632081 133249642558439190709974061)
  ·
    refine ⟨49968615959414696516240273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133249642558439190709974061 49968615959414696516240273)
    ·
      refine ⟨37476461969561022387180205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49968615959414696516240273 37476461969561022387180205)
      ·
        refine ⟨14053673238585383395192577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37476461969561022387180205 14053673238585383395192577)
        ·
          refine ⟨10540254928939037546394433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14053673238585383395192577 10540254928939037546394433)
          ·
            refine ⟨7905191196704278159795825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540254928939037546394433 7905191196704278159795825)
            ·
              refine ⟨5928893397528208619846869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905191196704278159795825 5928893397528208619846869)
              ·
                refine ⟨138958439004567389527661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5928893397528208619846869 138958439004567389527661)
                ·
                  rfl

theorem cell23_7306756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 7].length) (baseStart_7306756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306756 prefixEnd_7306756 := by exact prefixLift 7306756
  have htrace : WordTrace (prefixWord ++ tailWord_7306756) baseStart_7306756 baseEnd_7306756 := by
    simpa [prefixWord, tailWord_7306756, baseEnd_7306756] using wordTrace_append hprefix tailTrace_7306756
  have hstable : (prefixWord ++ tailWord_7306756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306756).length < 2 ^ (prefixWord ++ tailWord_7306756).sum := by decide
  have hdescent : baseEnd_7306756 < baseStart_7306756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306762 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7306762 : Nat := 118140960795 + 7306762 * 2 ^ 59
def prefixEnd_7306762 : Nat := 4983230072969 + 3 ^ 40 * 7306762 * 2
def baseEnd_7306762 : Nat := 3751880934007246493771819

theorem tailTrace_7306762 : CollatzResearch.WordTrace tailWord_7306762 prefixEnd_7306762 3751880934007246493771819 := by
  unfold tailWord_7306762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66624875988714161111166635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177666335969904429629777693 66624875988714161111166635)
  ·
    refine ⟨99937313983071241666749953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66624875988714161111166635 99937313983071241666749953)
    ·
      refine ⟨74952985487303431250062465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99937313983071241666749953 74952985487303431250062465)
      ·
        refine ⟨56214739115477573437546849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74952985487303431250062465 56214739115477573437546849)
        ·
          refine ⟨42161054336608180078160137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56214739115477573437546849 42161054336608180078160137)
          ·
            refine ⟨31620790752456135058620103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42161054336608180078160137 31620790752456135058620103)
            ·
              refine ⟨47431186128684202587930155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31620790752456135058620103 47431186128684202587930155)
              ·
                refine ⟨71146779193026303881895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47431186128684202587930155 71146779193026303881895233)
                ·
                  refine ⟨53360084394769727911421425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71146779193026303881895233 53360084394769727911421425)
                  ·
                    refine ⟨40020063296077295933566069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53360084394769727911421425 40020063296077295933566069)
                    ·
                      refine ⟨3751880934007246493771819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40020063296077295933566069 3751880934007246493771819)
                      ·
                        rfl

theorem cell23_7306762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7306762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306762 prefixEnd_7306762 := by exact prefixLift 7306762
  have htrace : WordTrace (prefixWord ++ tailWord_7306762) baseStart_7306762 baseEnd_7306762 := by
    simpa [prefixWord, tailWord_7306762, baseEnd_7306762] using wordTrace_append hprefix tailTrace_7306762
  have hstable : (prefixWord ++ tailWord_7306762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306762).length < 2 ^ (prefixWord ++ tailWord_7306762).sum := by decide
  have hdescent : baseEnd_7306762 < baseStart_7306762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306802 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7306802 : Nat := 118140960795 + 7306802 * 2 ^ 59
def prefixEnd_7306802 : Nat := 4983230072969 + 3 ^ 40 * 7306802 * 2
def baseEnd_7306802 : Nat := 3751901473233426337271635

theorem tailTrace_7306802 : CollatzResearch.WordTrace tailWord_7306802 prefixEnd_7306802 3751901473233426337271635 := by
  unfold tailWord_7306802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66625240718677932819030665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177667308583141154184081773 66625240718677932819030665)
  ·
    refine ⟨49968930539008449614272999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66625240718677932819030665 49968930539008449614272999)
    ·
      refine ⟨74953395808512674421409499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49968930539008449614272999 74953395808512674421409499)
      ·
        refine ⟨112430093712769011632114249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74953395808512674421409499 112430093712769011632114249)
        ·
          refine ⟨84322570284576758724085687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112430093712769011632114249 84322570284576758724085687)
          ·
            refine ⟨126483855426865138086128531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84322570284576758724085687 126483855426865138086128531)
            ·
              refine ⟨189725783140297707129192797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126483855426865138086128531 189725783140297707129192797)
              ·
                refine ⟨71147168677611640173447299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189725783140297707129192797 71147168677611640173447299)
                ·
                  refine ⟨106720753016417460260170949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71147168677611640173447299 106720753016417460260170949)
                  ·
                    refine ⟨20010141190578273798782053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106720753016417460260170949 20010141190578273798782053)
                    ·
                      refine ⟨3751901473233426337271635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20010141190578273798782053 3751901473233426337271635)
                      ·
                        rfl

theorem cell23_7306802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7306802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306802 prefixEnd_7306802 := by exact prefixLift 7306802
  have htrace : WordTrace (prefixWord ++ tailWord_7306802) baseStart_7306802 baseEnd_7306802 := by
    simpa [prefixWord, tailWord_7306802, baseEnd_7306802] using wordTrace_append hprefix tailTrace_7306802
  have hstable : (prefixWord ++ tailWord_7306802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306802).length < 2 ^ (prefixWord ++ tailWord_7306802).sum := by decide
  have hdescent : baseEnd_7306802 < baseStart_7306802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306849 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_7306849 : Nat := 118140960795 + 7306849 * 2 ^ 59
def prefixEnd_7306849 : Nat := 4983230072969 + 3 ^ 40 * 7306849 * 2
def baseEnd_7306849 : Nat := 3751925606824187653383919

theorem tailTrace_7306849 : CollatzResearch.WordTrace tailWord_7306849 prefixEnd_7306849 3751925606824187653383919 := by
  unfold tailWord_7306849
  simp only [CollatzResearch.WordTrace]
  refine ⟨266502677105541458303083601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177668451403694305535389067 266502677105541458303083601)
  ·
    refine ⟨199877007829156093727312701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266502677105541458303083601 199877007829156093727312701)
    ·
      refine ⟨74953877935933535147742263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199877007829156093727312701 74953877935933535147742263)
      ·
        refine ⟨112430816903900302721613395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74953877935933535147742263 112430816903900302721613395)
        ·
          refine ⟨168646225355850454082420093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112430816903900302721613395 168646225355850454082420093)
          ·
            refine ⟨63242334508443920280907535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168646225355850454082420093 63242334508443920280907535)
            ·
              refine ⟨94863501762665880421361303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63242334508443920280907535 94863501762665880421361303)
              ·
                refine ⟨142295252643998820632041955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94863501762665880421361303 142295252643998820632041955)
                ·
                  refine ⟨213442878965998230948062933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142295252643998820632041955 213442878965998230948062933)
                  ·
                    refine ⟨5002567475765583537845225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213442878965998230948062933 5002567475765583537845225)
                    ·
                      refine ⟨3751925606824187653383919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002567475765583537845225 3751925606824187653383919)
                      ·
                        rfl

theorem cell23_7306849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_7306849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306849 prefixEnd_7306849 := by exact prefixLift 7306849
  have htrace : WordTrace (prefixWord ++ tailWord_7306849) baseStart_7306849 baseEnd_7306849 := by
    simpa [prefixWord, tailWord_7306849, baseEnd_7306849] using wordTrace_append hprefix tailTrace_7306849
  have hstable : (prefixWord ++ tailWord_7306849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306849).length < 2 ^ (prefixWord ++ tailWord_7306849).sum := by decide
  have hdescent : baseEnd_7306849 < baseStart_7306849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306856 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7306856 : Nat := 118140960795 + 7306856 * 2 ^ 59
def prefixEnd_7306856 : Nat := 4983230072969 + 3 ^ 40 * 7306856 * 2
def baseEnd_7306856 : Nat := 3751929201188769125996387

theorem tailTrace_7306856 : CollatzResearch.WordTrace tailWord_7306856 prefixEnd_7306856 3751929201188769125996387 := by
  unfold tailWord_7306856
  simp only [CollatzResearch.WordTrace]
  refine ⟨133251466208258049249294211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177668621611010732332392281 133251466208258049249294211)
  ·
    refine ⟨199877199312387073873941317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133251466208258049249294211 199877199312387073873941317)
    ·
      refine ⟨37476974871072576351363997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199877199312387073873941317 37476974871072576351363997)
      ·
        refine ⟨14053865576652216131761499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37476974871072576351363997 14053865576652216131761499)
        ·
          refine ⟨21080798364978324197642249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14053865576652216131761499 21080798364978324197642249)
          ·
            refine ⟨15810598773733743148231687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21080798364978324197642249 15810598773733743148231687)
            ·
              refine ⟨23715898160600614722347531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15810598773733743148231687 23715898160600614722347531)
              ·
                refine ⟨35573847240900922083521297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23715898160600614722347531 35573847240900922083521297)
                ·
                  refine ⟨26680385430675691562640973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35573847240900922083521297 26680385430675691562640973)
                  ·
                    refine ⟨10005144536503384335990365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26680385430675691562640973 10005144536503384335990365)
                    ·
                      refine ⟨3751929201188769125996387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10005144536503384335990365 3751929201188769125996387)
                      ·
                        rfl

theorem cell23_7306856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7306856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306856 prefixEnd_7306856 := by exact prefixLift 7306856
  have htrace : WordTrace (prefixWord ++ tailWord_7306856) baseStart_7306856 baseEnd_7306856 := by
    simpa [prefixWord, tailWord_7306856, baseEnd_7306856] using wordTrace_append hprefix tailTrace_7306856
  have hstable : (prefixWord ++ tailWord_7306856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306856).length < 2 ^ (prefixWord ++ tailWord_7306856).sum := by decide
  have hdescent : baseEnd_7306856 < baseStart_7306856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306892 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7306892 : Nat := 118140960795 + 7306892 * 2 ^ 59
def prefixEnd_7306892 : Nat := 4983230072969 + 3 ^ 40 * 7306892 * 2
def baseEnd_7306892 : Nat := 3751947686492330985146221

theorem tailTrace_7306892 : CollatzResearch.WordTrace tailWord_7306892 prefixEnd_7306892 3751947686492330985146221 := by
  unfold tailWord_7306892
  simp only [CollatzResearch.WordTrace]
  refine ⟨133252122722192838323449465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177669496962923784431265953 133252122722192838323449465)
  ·
    refine ⟨99939092041644628742587099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133252122722192838323449465 99939092041644628742587099)
    ·
      refine ⟨149908638062466943113880649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99939092041644628742587099 149908638062466943113880649)
      ·
        refine ⟨112431478546850207335410487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149908638062466943113880649 112431478546850207335410487)
        ·
          refine ⟨168647217820275311003115731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112431478546850207335410487 168647217820275311003115731)
          ·
            refine ⟨252970826730412966504673597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168647217820275311003115731 252970826730412966504673597)
            ·
              refine ⟨94864060023904862439252599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252970826730412966504673597 94864060023904862439252599)
              ·
                refine ⟨142296090035857293658878899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94864060023904862439252599 142296090035857293658878899)
                ·
                  refine ⟨213444135053785940488318349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142296090035857293658878899 213444135053785940488318349)
                  ·
                    refine ⟨80041550645169727683119381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213444135053785940488318349 80041550645169727683119381)
                    ·
                      refine ⟨3751947686492330985146221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80041550645169727683119381 3751947686492330985146221)
                      ·
                        rfl

theorem cell23_7306892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7306892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306892 prefixEnd_7306892 := by exact prefixLift 7306892
  have htrace : WordTrace (prefixWord ++ tailWord_7306892) baseStart_7306892 baseEnd_7306892 := by
    simpa [prefixWord, tailWord_7306892, baseEnd_7306892] using wordTrace_append hprefix tailTrace_7306892
  have hstable : (prefixWord ++ tailWord_7306892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306892).length < 2 ^ (prefixWord ++ tailWord_7306892).sum := by decide
  have hdescent : baseEnd_7306892 < baseStart_7306892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306940 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_7306940 : Nat := 118140960795 + 7306940 * 2 ^ 59
def prefixEnd_7306940 : Nat := 4983230072969 + 3 ^ 40 * 7306940 * 2
def baseEnd_7306940 : Nat := 1250657444521248932448667

theorem tailTrace_7306940 : CollatzResearch.WordTrace tailWord_7306940 prefixEnd_7306940 1250657444521248932448667 := by
  unfold tailWord_7306940
  simp only [CollatzResearch.WordTrace]
  refine ⟨133252998074105890422323137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177670664098807853896430849 133252998074105890422323137)
  ·
    refine ⟨99939748555579417816742353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133252998074105890422323137 99939748555579417816742353)
    ·
      refine ⟨74954811416684563362556765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99939748555579417816742353 74954811416684563362556765)
      ·
        refine ⟨28108054281256711260958787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74954811416684563362556765 28108054281256711260958787)
        ·
          refine ⟨42162081421885066891438181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28108054281256711260958787 42162081421885066891438181)
          ·
            refine ⟨7905390266603450042144659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42162081421885066891438181 7905390266603450042144659)
            ·
              refine ⟨11858085399905175063216989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905390266603450042144659 11858085399905175063216989)
              ·
                refine ⟨4446782024964440648706371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11858085399905175063216989 4446782024964440648706371)
                ·
                  refine ⟨6670173037446660973059557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446782024964440648706371 6670173037446660973059557)
                  ·
                    refine ⟨1250657444521248932448667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670173037446660973059557 1250657444521248932448667)
                    ·
                      rfl

theorem cell23_7306940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_7306940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306940 prefixEnd_7306940 := by exact prefixLift 7306940
  have htrace : WordTrace (prefixWord ++ tailWord_7306940) baseStart_7306940 baseEnd_7306940 := by
    simpa [prefixWord, tailWord_7306940, baseEnd_7306940] using wordTrace_append hprefix tailTrace_7306940
  have hstable : (prefixWord ++ tailWord_7306940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306940).length < 2 ^ (prefixWord ++ tailWord_7306940).sum := by decide
  have hdescent : baseEnd_7306940 < baseStart_7306940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306950 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7306950 : Nat := 118140960795 + 7306950 * 2 ^ 59
def prefixEnd_7306950 : Nat := 4983230072969 + 3 ^ 40 * 7306950 * 2
def baseEnd_7306950 : Nat := 3751977468370291758220955

theorem tailTrace_7306950 : CollatzResearch.WordTrace tailWord_7306950 prefixEnd_7306950 3751977468370291758220955 := by
  unfold tailWord_7306950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328323777442986017265947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177670907252117035035006869 8328323777442986017265947)
  ·
    refine ⟨12492485666164479025898921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328323777442986017265947 12492485666164479025898921)
    ·
      refine ⟨9369364249623359269424191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12492485666164479025898921 9369364249623359269424191)
      ·
        refine ⟨14054046374435038904136287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369364249623359269424191 14054046374435038904136287)
        ·
          refine ⟨21081069561652558356204431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14054046374435038904136287 21081069561652558356204431)
          ·
            refine ⟨31621604342478837534306647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21081069561652558356204431 31621604342478837534306647)
            ·
              refine ⟨47432406513718256301459971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31621604342478837534306647 47432406513718256301459971)
              ·
                refine ⟨71148609770577384452189957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47432406513718256301459971 71148609770577384452189957)
                ·
                  refine ⟨13340364331983259584785617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71148609770577384452189957 13340364331983259584785617)
                  ·
                    refine ⟨10005273248987444688589213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13340364331983259584785617 10005273248987444688589213)
                    ·
                      refine ⟨3751977468370291758220955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10005273248987444688589213 3751977468370291758220955)
                      ·
                        rfl

theorem cell23_7306950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7306950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306950 prefixEnd_7306950 := by exact prefixLift 7306950
  have htrace : WordTrace (prefixWord ++ tailWord_7306950) baseStart_7306950 baseEnd_7306950 := by
    simpa [prefixWord, tailWord_7306950, baseEnd_7306950] using wordTrace_append hprefix tailTrace_7306950
  have hstable : (prefixWord ++ tailWord_7306950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306950).length < 2 ^ (prefixWord ++ tailWord_7306950).sum := by decide
  have hdescent : baseEnd_7306950 < baseStart_7306950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306983 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 3, 5]
def baseStart_7306983 : Nat := 118140960795 + 7306983 * 2 ^ 59
def prefixEnd_7306983 : Nat := 4983230072969 + 3 ^ 40 * 7306983 * 2
def baseEnd_7306983 : Nat := 1250664804410630043036101

theorem tailTrace_7306983 : CollatzResearch.WordTrace tailWord_7306983 prefixEnd_7306983 1250664804410630043036101 := by
  unfold tailWord_7306983
  simp only [CollatzResearch.WordTrace]
  refine ⟨266507564487055999188461603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177671709658037332792307735 266507564487055999188461603)
  ·
    refine ⟨399761346730583998782692405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266507564487055999188461603 399761346730583998782692405)
    ·
      refine ⟨37477626255992249885877413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399761346730583998782692405 37477626255992249885877413)
      ·
        refine ⟨7027054922998546853602015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37477626255992249885877413 7027054922998546853602015)
        ·
          refine ⟨10540582384497820280403023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027054922998546853602015 10540582384497820280403023)
          ·
            refine ⟨15810873576746730420604535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540582384497820280403023 15810873576746730420604535)
            ·
              refine ⟨23716310365120095630906803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15810873576746730420604535 23716310365120095630906803)
              ·
                refine ⟨35574465547680143446360205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23716310365120095630906803 35574465547680143446360205)
                ·
                  refine ⟨13340424580380053792385077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35574465547680143446360205 13340424580380053792385077)
                  ·
                    refine ⟨1250664804410630043036101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13340424580380053792385077 1250664804410630043036101)
                    ·
                      rfl

theorem cell23_7306983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_7306983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306983 prefixEnd_7306983 := by exact prefixLift 7306983
  have htrace : WordTrace (prefixWord ++ tailWord_7306983) baseStart_7306983 baseEnd_7306983 := by
    simpa [prefixWord, tailWord_7306983, baseEnd_7306983] using wordTrace_append hprefix tailTrace_7306983
  have hstable : (prefixWord ++ tailWord_7306983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306983).length < 2 ^ (prefixWord ++ tailWord_7306983).sum := by decide
  have hdescent : baseEnd_7306983 < baseStart_7306983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306986 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_7306986 : Nat := 118140960795 + 7306986 * 2 ^ 59
def prefixEnd_7306986 : Nat := 4983230072969 + 3 ^ 40 * 7306986 * 2
def baseEnd_7306986 : Nat := 3751995953673853617370789

theorem tailTrace_7306986 : CollatzResearch.WordTrace tailWord_7306986 prefixEnd_7306986 3751995953673853617370789 := by
  unfold tailWord_7306986
  simp only [CollatzResearch.WordTrace]
  refine ⟨66626918476511282675205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177671782604030087133880541 66626918476511282675205203)
  ·
    refine ⟨99940377714766924012807805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66626918476511282675205203 99940377714766924012807805)
    ·
      refine ⟨37477641643037596504802927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99940377714766924012807805 37477641643037596504802927)
      ·
        refine ⟨56216462464556394757204391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37477641643037596504802927 56216462464556394757204391)
        ·
          refine ⟨84324693696834592135806587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56216462464556394757204391 84324693696834592135806587)
          ·
            refine ⟨126487040545251888203709881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84324693696834592135806587 126487040545251888203709881)
            ·
              refine ⟨94865280408938916152782411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126487040545251888203709881 94865280408938916152782411)
              ·
                refine ⟨142297920613408374229173617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94865280408938916152782411 142297920613408374229173617)
                ·
                  refine ⟨106723440460056280671880213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142297920613408374229173617 106723440460056280671880213)
                  ·
                    refine ⟨5002661271565138156494385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106723440460056280671880213 5002661271565138156494385)
                    ·
                      refine ⟨3751995953673853617370789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002661271565138156494385 3751995953673853617370789)
                      ·
                        rfl

theorem cell23_7306986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_7306986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306986 prefixEnd_7306986 := by exact prefixLift 7306986
  have htrace : WordTrace (prefixWord ++ tailWord_7306986) baseStart_7306986 baseEnd_7306986 := by
    simpa [prefixWord, tailWord_7306986, baseEnd_7306986] using wordTrace_append hprefix tailTrace_7306986
  have hstable : (prefixWord ++ tailWord_7306986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306986).length < 2 ^ (prefixWord ++ tailWord_7306986).sum := by decide
  have hdescent : baseEnd_7306986 < baseStart_7306986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7306999 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_7306999 : Nat := 118140960795 + 7306999 * 2 ^ 59
def prefixEnd_7306999 : Nat := 4983230072969 + 3 ^ 40 * 7306999 * 2
def baseEnd_7306999 : Nat := 3752002628922362066508229

theorem tailTrace_7306999 : CollatzResearch.WordTrace tailWord_7306999 prefixEnd_7306999 3752002628922362066508229 := by
  unfold tailWord_7306999
  simp only [CollatzResearch.WordTrace]
  refine ⟨266508148054998033921044051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177672098703332022614029367 266508148054998033921044051)
  ·
    refine ⟨399762222082497050881566077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266508148054998033921044051 399762222082497050881566077)
    ·
      refine ⟨149910833280936394080587279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399762222082497050881566077 149910833280936394080587279)
      ·
        refine ⟨224866249921404591120880919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149910833280936394080587279 224866249921404591120880919)
        ·
          refine ⟨337299374882106886681321379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224866249921404591120880919 337299374882106886681321379)
          ·
            refine ⟨505949062323160330021982069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337299374882106886681321379 505949062323160330021982069)
            ·
              refine ⟨47432724592796280939560819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505949062323160330021982069 47432724592796280939560819)
              ·
                refine ⟨71149086889194421409341229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47432724592796280939560819 71149086889194421409341229)
                ·
                  refine ⟨26680907583447908028502961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71149086889194421409341229 26680907583447908028502961)
                  ·
                    refine ⟨20010680687585931021377221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26680907583447908028502961 20010680687585931021377221)
                    ·
                      refine ⟨3752002628922362066508229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20010680687585931021377221 3752002628922362066508229)
                      ·
                        rfl

theorem cell23_7306999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_7306999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7306999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7306999 prefixEnd_7306999 := by exact prefixLift 7306999
  have htrace : WordTrace (prefixWord ++ tailWord_7306999) baseStart_7306999 baseEnd_7306999 := by
    simpa [prefixWord, tailWord_7306999, baseEnd_7306999] using wordTrace_append hprefix tailTrace_7306999
  have hstable : (prefixWord ++ tailWord_7306999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7306999).length < 2 ^ (prefixWord ++ tailWord_7306999).sum := by decide
  have hdescent : baseEnd_7306999 < baseStart_7306999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7306999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307039 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 7]
def baseStart_7307039 : Nat := 118140960795 + 7307039 * 2 ^ 59
def prefixEnd_7307039 : Nat := 4983230072969 + 3 ^ 40 * 7307039 * 2
def baseEnd_7307039 : Nat := 1250674389382847303336015

theorem tailTrace_7307039 : CollatzResearch.WordTrace tailWord_7307039 prefixEnd_7307039 1250674389382847303336015 := by
  unfold tailWord_7307039
  simp only [CollatzResearch.WordTrace]
  refine ⟨266509606974853120752500171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177673071316568747168333447 266509606974853120752500171)
  ·
    refine ⟨399764410462279681128750257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266509606974853120752500171 399764410462279681128750257)
    ·
      refine ⟨299823307846709760846562693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399764410462279681128750257 299823307846709760846562693)
      ·
        refine ⟨56216870221258080158730505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299823307846709760846562693 56216870221258080158730505)
        ·
          refine ⟨42162652665943560119047879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56216870221258080158730505 42162652665943560119047879)
          ·
            refine ⟨63243978998915340178571819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42162652665943560119047879 63243978998915340178571819)
            ·
              refine ⟨94865968498373010267857729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63243978998915340178571819 94865968498373010267857729)
              ·
                refine ⟨71149476373779757700893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94865968498373010267857729 71149476373779757700893297)
                ·
                  refine ⟨53362107280334818275669973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71149476373779757700893297 53362107280334818275669973)
                  ·
                    refine ⟨1250674389382847303336015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53362107280334818275669973 1250674389382847303336015)
                    ·
                      rfl

theorem cell23_7307039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_7307039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307039 prefixEnd_7307039 := by exact prefixLift 7307039
  have htrace : WordTrace (prefixWord ++ tailWord_7307039) baseStart_7307039 baseEnd_7307039 := by
    simpa [prefixWord, tailWord_7307039, baseEnd_7307039] using wordTrace_append hprefix tailTrace_7307039
  have hstable : (prefixWord ++ tailWord_7307039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307039).length < 2 ^ (prefixWord ++ tailWord_7307039).sum := by decide
  have hdescent : baseEnd_7307039 < baseStart_7307039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307054 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7307054 : Nat := 118140960795 + 7307054 * 2 ^ 59
def prefixEnd_7307054 : Nat := 4983230072969 + 3 ^ 40 * 7307054 * 2
def baseEnd_7307054 : Nat := 3752030870358359351320477

theorem tailTrace_7307054 : CollatzResearch.WordTrace tailWord_7307054 prefixEnd_7307054 3752030870358359351320477 := by
  unfold tailWord_7307054
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313769258724847289287027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177673436046532518876197477 33313769258724847289287027)
  ·
    refine ⟨49970653888087270933930541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33313769258724847289287027 49970653888087270933930541)
    ·
      refine ⟨18738995208032726600223953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49970653888087270933930541 18738995208032726600223953)
      ·
        refine ⟨14054246406024544950167965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18738995208032726600223953 14054246406024544950167965)
        ·
          refine ⟨5270342402259204356312987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14054246406024544950167965 5270342402259204356312987)
          ·
            refine ⟨7905513603388806534469481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270342402259204356312987 7905513603388806534469481)
            ·
              refine ⟨5929135202541604900852111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905513603388806534469481 5929135202541604900852111)
              ·
                refine ⟨8893702803812407351278167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929135202541604900852111 8893702803812407351278167)
                ·
                  refine ⟨13340554205718611026917251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893702803812407351278167 13340554205718611026917251)
                  ·
                    refine ⟨20010831308577916540375877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13340554205718611026917251 20010831308577916540375877)
                    ·
                      refine ⟨3752030870358359351320477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20010831308577916540375877 3752030870358359351320477)
                      ·
                        rfl

theorem cell23_7307054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7307054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307054 prefixEnd_7307054 := by exact prefixLift 7307054
  have htrace : WordTrace (prefixWord ++ tailWord_7307054) baseStart_7307054 baseEnd_7307054 := by
    simpa [prefixWord, tailWord_7307054, baseEnd_7307054] using wordTrace_append hprefix tailTrace_7307054
  have hstable : (prefixWord ++ tailWord_7307054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307054).length < 2 ^ (prefixWord ++ tailWord_7307054).sum := by decide
  have hdescent : baseEnd_7307054 < baseStart_7307054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307070 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_7307070 : Nat := 118140960795 + 7307070 * 2 ^ 59
def prefixEnd_7307070 : Nat := 4983230072969 + 3 ^ 40 * 7307070 * 2
def baseEnd_7307070 : Nat := 3752039086048831288720403

theorem tailTrace_7307070 : CollatzResearch.WordTrace tailWord_7307070 prefixEnd_7307070 3752039086048831288720403 := by
  unfold tailWord_7307070
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313842204717601630859833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177673825091827208697919109 33313842204717601630859833)
  ·
    refine ⟨24985381653538201223144875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33313842204717601630859833 24985381653538201223144875)
    ·
      refine ⟨37478072480307301834717313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24985381653538201223144875 37478072480307301834717313)
      ·
        refine ⟨28108554360230476376037985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37478072480307301834717313 28108554360230476376037985)
        ·
          refine ⟨21081415770172857282028489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28108554360230476376037985 21081415770172857282028489)
          ·
            refine ⟨15811061827629642961521367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21081415770172857282028489 15811061827629642961521367)
            ·
              refine ⟨23716592741444464442282051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15811061827629642961521367 23716592741444464442282051)
              ·
                refine ⟨35574889112166696663423077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23716592741444464442282051 35574889112166696663423077)
                ·
                  refine ⟨6670291708531255624391827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35574889112166696663423077 6670291708531255624391827)
                  ·
                    refine ⟨10005437562796883436587741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670291708531255624391827 10005437562796883436587741)
                    ·
                      refine ⟨3752039086048831288720403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10005437562796883436587741 3752039086048831288720403)
                      ·
                        rfl

theorem cell23_7307070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_7307070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307070 prefixEnd_7307070 := by exact prefixLift 7307070
  have htrace : WordTrace (prefixWord ++ tailWord_7307070) baseStart_7307070 baseEnd_7307070 := by
    simpa [prefixWord, tailWord_7307070, baseEnd_7307070] using wordTrace_append hprefix tailTrace_7307070
  have hstable : (prefixWord ++ tailWord_7307070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307070).length < 2 ^ (prefixWord ++ tailWord_7307070).sum := by decide
  have hdescent : baseEnd_7307070 < baseStart_7307070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307119 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_7307119 : Nat := 118140960795 + 7307119 * 2 ^ 59
def prefixEnd_7307119 : Nat := 4983230072969 + 3 ^ 40 * 7307119 * 2
def baseEnd_7307119 : Nat := 3752064246600901597007677

theorem tailTrace_7307119 : CollatzResearch.WordTrace tailWord_7307119 prefixEnd_7307119 3752064246600901597007677 := by
  unfold tailWord_7307119
  simp only [CollatzResearch.WordTrace]
  refine ⟨266512524814563294415412411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177675016543042196276941607 266512524814563294415412411)
  ·
    refine ⟨399768787221844941623118617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266512524814563294415412411 399768787221844941623118617)
    ·
      refine ⟨299826590416383706217338963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399768787221844941623118617 299826590416383706217338963)
      ·
        refine ⟨449739885624575559326008445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299826590416383706217338963 449739885624575559326008445)
        ·
          refine ⟨168652457109215834747253167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449739885624575559326008445 168652457109215834747253167)
          ·
            refine ⟨252978685663823752120879751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168652457109215834747253167 252978685663823752120879751)
            ·
              refine ⟨379468028495735628181319627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252978685663823752120879751 379468028495735628181319627)
              ·
                refine ⟨569202042743603442271979441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379468028495735628181319627 569202042743603442271979441)
                ·
                  refine ⟨426901532057702581703984581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569202042743603442271979441 426901532057702581703984581)
                  ·
                    refine ⟨80044037260819234069497109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426901532057702581703984581 80044037260819234069497109)
                    ·
                      refine ⟨3752064246600901597007677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80044037260819234069497109 3752064246600901597007677)
                      ·
                        rfl

theorem cell23_7307119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_7307119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307119 prefixEnd_7307119 := by exact prefixLift 7307119
  have htrace : WordTrace (prefixWord ++ tailWord_7307119) baseStart_7307119 baseEnd_7307119 := by
    simpa [prefixWord, tailWord_7307119, baseEnd_7307119] using wordTrace_append hprefix tailTrace_7307119
  have hstable : (prefixWord ++ tailWord_7307119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307119).length < 2 ^ (prefixWord ++ tailWord_7307119).sum := by decide
  have hdescent : baseEnd_7307119 < baseStart_7307119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307183 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 4, 2]
def baseStart_7307183 : Nat := 118140960795 + 7307183 * 2 ^ 59
def prefixEnd_7307183 : Nat := 4983230072969 + 3 ^ 40 * 7307183 * 2
def baseEnd_7307183 : Nat := 3752097109362789346607383

theorem tailTrace_7307183 : CollatzResearch.WordTrace tailWord_7307183 prefixEnd_7307183 3752097109362789346607383 := by
  unfold tailWord_7307183
  simp only [CollatzResearch.WordTrace]
  refine ⟨266514859086331433345742203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177676572724220955563828135 266514859086331433345742203)
  ·
    refine ⟨399772288629497150018613305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266514859086331433345742203 399772288629497150018613305)
    ·
      refine ⟨299829216472122862513959979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399772288629497150018613305 299829216472122862513959979)
      ·
        refine ⟨449743824708184293770939969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299829216472122862513959979 449743824708184293770939969)
        ·
          refine ⟨337307868531138220328204977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449743824708184293770939969 337307868531138220328204977)
          ·
            refine ⟨252980901398353665246153733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337307868531138220328204977 252980901398353665246153733)
            ·
              refine ⟨47433919012191312233653825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252980901398353665246153733 47433919012191312233653825)
              ·
                refine ⟨35575439259143484175240369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47433919012191312233653825 35575439259143484175240369)
                ·
                  refine ⟨26681579444357613131430277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35575439259143484175240369 26681579444357613131430277)
                  ·
                    refine ⟨5002796145817052462143177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26681579444357613131430277 5002796145817052462143177)
                    ·
                      refine ⟨3752097109362789346607383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002796145817052462143177 3752097109362789346607383)
                      ·
                        rfl

theorem cell23_7307183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4, 2].length) (baseStart_7307183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307183 prefixEnd_7307183 := by exact prefixLift 7307183
  have htrace : WordTrace (prefixWord ++ tailWord_7307183) baseStart_7307183 baseEnd_7307183 := by
    simpa [prefixWord, tailWord_7307183, baseEnd_7307183] using wordTrace_append hprefix tailTrace_7307183
  have hstable : (prefixWord ++ tailWord_7307183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307183).length < 2 ^ (prefixWord ++ tailWord_7307183).sum := by decide
  have hdescent : baseEnd_7307183 < baseStart_7307183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307193 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_7307193 : Nat := 118140960795 + 7307193 * 2 ^ 59
def prefixEnd_7307193 : Nat := 4983230072969 + 3 ^ 40 * 7307193 * 2
def baseEnd_7307193 : Nat := 1250700748056444769160779

theorem tailTrace_7307193 : CollatzResearch.WordTrace tailWord_7307193 prefixEnd_7307193 1250700748056444769160779 := by
  unfold tailWord_7307193
  simp only [CollatzResearch.WordTrace]
  refine ⟨266515223816295205053606233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177676815877530136702404155 266515223816295205053606233)
  ·
    refine ⟨199886417862221403790204675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266515223816295205053606233 199886417862221403790204675)
    ·
      refine ⟨299829626793332105685307013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199886417862221403790204675 299829626793332105685307013)
      ·
        refine ⟨56218055023749769815995065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299829626793332105685307013 56218055023749769815995065)
        ·
          refine ⟨42163541267812327361996299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56218055023749769815995065 42163541267812327361996299)
          ·
            refine ⟨63245311901718491042994449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42163541267812327361996299 63245311901718491042994449)
            ·
              refine ⟨47433983926288868282245837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63245311901718491042994449 47433983926288868282245837)
              ·
                refine ⟨17787743972358325605842189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47433983926288868282245837 17787743972358325605842189)
                ·
                  refine ⟨6670403989634372102190821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17787743972358325605842189 6670403989634372102190821)
                  ·
                    refine ⟨1250700748056444769160779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670403989634372102190821 1250700748056444769160779)
                    ·
                      rfl

theorem cell23_7307193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_7307193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307193 prefixEnd_7307193 := by exact prefixLift 7307193
  have htrace : WordTrace (prefixWord ++ tailWord_7307193) baseStart_7307193 baseEnd_7307193 := by
    simpa [prefixWord, tailWord_7307193, baseEnd_7307193] using wordTrace_append hprefix tailTrace_7307193
  have hstable : (prefixWord ++ tailWord_7307193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307193).length < 2 ^ (prefixWord ++ tailWord_7307193).sum := by decide
  have hdescent : baseEnd_7307193 < baseStart_7307193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307283 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 4, 4]
def baseStart_7307283 : Nat := 118140960795 + 7307283 * 2 ^ 59
def prefixEnd_7307283 : Nat := 4983230072969 + 3 ^ 40 * 7307283 * 2
def baseEnd_7307283 : Nat := 1250716152476079651785641

theorem tailTrace_7307283 : CollatzResearch.WordTrace tailWord_7307283 prefixEnd_7307283 1250716152476079651785641 := by
  unfold tailWord_7307283
  simp only [CollatzResearch.WordTrace]
  refine ⟨266518506385969150424382503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177679004257312766949588335 266518506385969150424382503)
  ·
    refine ⟨399777759578953725636573755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266518506385969150424382503 399777759578953725636573755)
    ·
      refine ⟨599666639368430588454860633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399777759578953725636573755 599666639368430588454860633)
      ·
        refine ⟨449749979526322941341145475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599666639368430588454860633 449749979526322941341145475)
        ·
          refine ⟨674624969289484412011718213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449749979526322941341145475 674624969289484412011718213)
          ·
            refine ⟨126492181741778327252197165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 674624969289484412011718213 126492181741778327252197165)
            ·
              refine ⟨47434568153166872719573937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126492181741778327252197165 47434568153166872719573937)
              ·
                refine ⟨35575926114875154539680453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47434568153166872719573937 35575926114875154539680453)
                ·
                  refine ⟨6670486146539091476190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35575926114875154539680453 6670486146539091476190085)
                  ·
                    refine ⟨1250716152476079651785641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670486146539091476190085 1250716152476079651785641)
                    ·
                      rfl

theorem cell23_7307283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 4].length) (baseStart_7307283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307283 prefixEnd_7307283 := by exact prefixLift 7307283
  have htrace : WordTrace (prefixWord ++ tailWord_7307283) baseStart_7307283 baseEnd_7307283 := by
    simpa [prefixWord, tailWord_7307283, baseEnd_7307283] using wordTrace_append hprefix tailTrace_7307283
  have hstable : (prefixWord ++ tailWord_7307283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307283).length < 2 ^ (prefixWord ++ tailWord_7307283).sum := by decide
  have hdescent : baseEnd_7307283 < baseStart_7307283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307290 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_7307290 : Nat := 118140960795 + 7307290 * 2 ^ 59
def prefixEnd_7307290 : Nat := 4983230072969 + 3 ^ 40 * 7307290 * 2
def baseEnd_7307290 : Nat := 3752152051792820427969391

theorem tailTrace_7307290 : CollatzResearch.WordTrace tailWord_7307290 prefixEnd_7307290 3752152051792820427969391 := by
  unfold tailWord_7307290
  simp only [CollatzResearch.WordTrace]
  refine ⟨66629690424235947654971831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177679174464629193746591549 66629690424235947654971831)
  ·
    refine ⟨99944535636353921482457747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66629690424235947654971831 99944535636353921482457747)
    ·
      refine ⟨149916803454530882223686621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99944535636353921482457747 149916803454530882223686621)
      ·
        refine ⟨56218801295449080833882483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149916803454530882223686621 56218801295449080833882483)
        ·
          refine ⟨84328201943173621250823725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56218801295449080833882483 84328201943173621250823725)
          ·
            refine ⟨31623075728690107969058897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84328201943173621250823725 31623075728690107969058897)
            ·
              refine ⟨23717306796517580976794173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31623075728690107969058897 23717306796517580976794173)
              ·
                refine ⟨8893990048694092866297815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23717306796517580976794173 8893990048694092866297815)
                ·
                  refine ⟨13340985073041139299446723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893990048694092866297815 13340985073041139299446723)
                  ·
                    refine ⟨20011477609561708949170085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13340985073041139299446723 20011477609561708949170085)
                    ·
                      refine ⟨3752152051792820427969391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20011477609561708949170085 3752152051792820427969391)
                      ·
                        rfl

theorem cell23_7307290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_7307290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307290 prefixEnd_7307290 := by exact prefixLift 7307290
  have htrace : WordTrace (prefixWord ++ tailWord_7307290) baseStart_7307290 baseEnd_7307290 := by
    simpa [prefixWord, tailWord_7307290, baseEnd_7307290] using wordTrace_append hprefix tailTrace_7307290
  have hstable : (prefixWord ++ tailWord_7307290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307290).length < 2 ^ (prefixWord ++ tailWord_7307290).sum := by decide
  have hdescent : baseEnd_7307290 < baseStart_7307290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307310 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7307310 : Nat := 118140960795 + 7307310 * 2 ^ 59
def prefixEnd_7307310 : Nat := 4983230072969 + 3 ^ 40 * 7307310 * 2
def baseEnd_7307310 : Nat := 3752162321405910349719299

theorem tailTrace_7307310 : CollatzResearch.WordTrace tailWord_7307310 prefixEnd_7307310 3752162321405910349719299 := by
  unfold tailWord_7307310
  simp only [CollatzResearch.WordTrace]
  refine ⟨33314936394608916754451923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177679660771247556023743589 33314936394608916754451923)
  ·
    refine ⟨49972404591913375131677885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33314936394608916754451923 49972404591913375131677885)
    ·
      refine ⟨18739651721967515674379207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49972404591913375131677885 18739651721967515674379207)
      ·
        refine ⟨28109477582951273511568811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18739651721967515674379207 28109477582951273511568811)
        ·
          refine ⟨42164216374426910267353217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28109477582951273511568811 42164216374426910267353217)
          ·
            refine ⟨31623162280820182700514913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42164216374426910267353217 31623162280820182700514913)
            ·
              refine ⟨23717371710615137025386185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31623162280820182700514913 23717371710615137025386185)
              ·
                refine ⟨17788028782961352769039639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23717371710615137025386185 17788028782961352769039639)
                ·
                  refine ⟨26682043174442029153559459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788028782961352769039639 26682043174442029153559459)
                  ·
                    refine ⟨40023064761663043730339189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26682043174442029153559459 40023064761663043730339189)
                    ·
                      refine ⟨3752162321405910349719299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40023064761663043730339189 3752162321405910349719299)
                      ·
                        rfl

theorem cell23_7307310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7307310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307310 prefixEnd_7307310 := by exact prefixLift 7307310
  have htrace : WordTrace (prefixWord ++ tailWord_7307310) baseStart_7307310 baseEnd_7307310 := by
    simpa [prefixWord, tailWord_7307310, baseEnd_7307310] using wordTrace_append hprefix tailTrace_7307310
  have hstable : (prefixWord ++ tailWord_7307310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307310).length < 2 ^ (prefixWord ++ tailWord_7307310).sum := by decide
  have hdescent : baseEnd_7307310 < baseStart_7307310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307313 : List Nat := [1, 2, 2, 3, 1, 4, 2, 8]
def baseStart_7307313 : Nat := 118140960795 + 7307313 * 2 ^ 59
def prefixEnd_7307313 : Nat := 4983230072969 + 3 ^ 40 * 7307313 * 2
def baseEnd_7307313 : Nat := 138969031920291623628955

theorem tailTrace_7307313 : CollatzResearch.WordTrace tailWord_7307313 prefixEnd_7307313 138969031920291623628955 := by
  unfold tailWord_7307313
  simp only [CollatzResearch.WordTrace]
  refine ⟨266519600575860465547974593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177679733717240310365316395 266519600575860465547974593)
  ·
    refine ⟨199889700431895349160980945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266519600575860465547974593 199889700431895349160980945)
    ·
      refine ⟨149917275323921511870735709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199889700431895349160980945 149917275323921511870735709)
      ·
        refine ⟨56218978246470566951525891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149917275323921511870735709 56218978246470566951525891)
        ·
          refine ⟨84328467369705850427288837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56218978246470566951525891 84328467369705850427288837)
          ·
            refine ⟨15811587631819846955116657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84328467369705850427288837 15811587631819846955116657)
            ·
              refine ⟨11858690723864885216337493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15811587631819846955116657 11858690723864885216337493)
              ·
                refine ⟨138969031920291623628955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11858690723864885216337493 138969031920291623628955)
                ·
                  rfl

theorem cell23_7307313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 8].length) (baseStart_7307313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307313 prefixEnd_7307313 := by exact prefixLift 7307313
  have htrace : WordTrace (prefixWord ++ tailWord_7307313) baseStart_7307313 baseEnd_7307313 := by
    simpa [prefixWord, tailWord_7307313, baseEnd_7307313] using wordTrace_append hprefix tailTrace_7307313
  have hstable : (prefixWord ++ tailWord_7307313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307313).length < 2 ^ (prefixWord ++ tailWord_7307313).sum := by decide
  have hdescent : baseEnd_7307313 < baseStart_7307313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307317 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7307317 : Nat := 118140960795 + 7307317 * 2 ^ 59
def prefixEnd_7307317 : Nat := 4983230072969 + 3 ^ 40 * 7307317 * 2
def baseEnd_7307317 : Nat := 1250721971923497274110589

theorem tailTrace_7307317 : CollatzResearch.WordTrace tailWord_7307317 prefixEnd_7307317 1250721971923497274110589 := by
  unfold tailWord_7307317
  simp only [CollatzResearch.WordTrace]
  refine ⟨266519746467845974231120205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177679830978563982820746803 266519746467845974231120205)
  ·
    refine ⟨99944904925442240336670077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266519746467845974231120205 99944904925442240336670077)
    ·
      refine ⟨37479339347040840126251279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99944904925442240336670077 37479339347040840126251279)
      ·
        refine ⟨56219009020561260189376919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37479339347040840126251279 56219009020561260189376919)
        ·
          refine ⟨84328513530841890284065379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56219009020561260189376919 84328513530841890284065379)
          ·
            refine ⟨126492770296262835426098069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84328513530841890284065379 126492770296262835426098069)
            ·
              refine ⟨5929348607637320410598347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126492770296262835426098069 5929348607637320410598347)
              ·
                refine ⟨8894022911455980615897521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929348607637320410598347 8894022911455980615897521)
                ·
                  refine ⟨6670517183591985461923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894022911455980615897521 6670517183591985461923141)
                  ·
                    refine ⟨1250721971923497274110589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670517183591985461923141 1250721971923497274110589)
                    ·
                      rfl

theorem cell23_7307317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7307317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307317 prefixEnd_7307317 := by exact prefixLift 7307317
  have htrace : WordTrace (prefixWord ++ tailWord_7307317) baseStart_7307317 baseEnd_7307317 := by
    simpa [prefixWord, tailWord_7307317, baseEnd_7307317] using wordTrace_append hprefix tailTrace_7307317
  have hstable : (prefixWord ++ tailWord_7307317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307317).length < 2 ^ (prefixWord ++ tailWord_7307317).sum := by decide
  have hdescent : baseEnd_7307317 < baseStart_7307317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307340 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7307340 : Nat := 118140960795 + 7307340 * 2 ^ 59
def prefixEnd_7307340 : Nat := 4983230072969 + 3 ^ 40 * 7307340 * 2
def baseEnd_7307340 : Nat := 3752177725825545232344161

theorem tailTrace_7307340 : CollatzResearch.WordTrace tailWord_7307340 prefixEnd_7307340 3752177725825545232344161 := by
  unfold tailWord_7307340
  simp only [CollatzResearch.WordTrace]
  refine ⟨133260292673381324579603737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177680390231175099439471649 133260292673381324579603737)
  ·
    refine ⟨99945219505035993434702803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133260292673381324579603737 99945219505035993434702803)
    ·
      refine ⟨149917829257553990152054205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99945219505035993434702803 149917829257553990152054205)
      ·
        refine ⟨56219185971582746307020327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149917829257553990152054205 56219185971582746307020327)
        ·
          refine ⟨84328778957374119460530491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56219185971582746307020327 84328778957374119460530491)
          ·
            refine ⟨126493168436061179190795737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84328778957374119460530491 126493168436061179190795737)
            ·
              refine ⟨94869876327045884393096803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126493168436061179190795737 94869876327045884393096803)
              ·
                refine ⟨142304814490568826589645205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94869876327045884393096803 142304814490568826589645205)
                ·
                  refine ⟨6670538179245413746389619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142304814490568826589645205 6670538179245413746389619)
                  ·
                    refine ⟨10005807268868120619584429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670538179245413746389619 10005807268868120619584429)
                    ·
                      refine ⟨3752177725825545232344161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10005807268868120619584429 3752177725825545232344161)
                      ·
                        rfl

theorem cell23_7307340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7307340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307340 prefixEnd_7307340 := by exact prefixLift 7307340
  have htrace : WordTrace (prefixWord ++ tailWord_7307340) baseStart_7307340 baseEnd_7307340 := by
    simpa [prefixWord, tailWord_7307340, baseEnd_7307340] using wordTrace_append hprefix tailTrace_7307340
  have hstable : (prefixWord ++ tailWord_7307340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307340).length < 2 ^ (prefixWord ++ tailWord_7307340).sum := by decide
  have hdescent : baseEnd_7307340 < baseStart_7307340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307341 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7307341 : Nat := 118140960795 + 7307341 * 2 ^ 59
def prefixEnd_7307341 : Nat := 4983230072969 + 3 ^ 40 * 7307341 * 2
def baseEnd_7307341 : Nat := 3752178239306199728431657

theorem tailTrace_7307341 : CollatzResearch.WordTrace tailWord_7307341 prefixEnd_7307341 3752178239306199728431657 := by
  unfold tailWord_7307341
  simp only [CollatzResearch.WordTrace]
  refine ⟨266520621819759026329993877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177680414546506017553329251 266520621819759026329993877)
  ·
    refine ⟨12493154147801204359218463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266520621819759026329993877 12493154147801204359218463)
    ·
      refine ⟨18739731221701806538827695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12493154147801204359218463 18739731221701806538827695)
      ·
        refine ⟨28109596832552709808241543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18739731221701806538827695 28109596832552709808241543)
        ·
          refine ⟨42164395248829064712362315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28109596832552709808241543 42164395248829064712362315)
          ·
            refine ⟨63246592873243597068543473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42164395248829064712362315 63246592873243597068543473)
            ·
              refine ⟨47434944654932697801407605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63246592873243597068543473 47434944654932697801407605)
              ·
                refine ⟨4447026061399940418881963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47434944654932697801407605 4447026061399940418881963)
                ·
                  refine ⟨6670539092099910628322945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447026061399940418881963 6670539092099910628322945)
                  ·
                    refine ⟨5002904319074932971242209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670539092099910628322945 5002904319074932971242209)
                    ·
                      refine ⟨3752178239306199728431657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002904319074932971242209 3752178239306199728431657)
                      ·
                        rfl

theorem cell23_7307341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7307341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307341 prefixEnd_7307341 := by exact prefixLift 7307341
  have htrace : WordTrace (prefixWord ++ tailWord_7307341) baseStart_7307341 baseEnd_7307341 := by
    simpa [prefixWord, tailWord_7307341, baseEnd_7307341] using wordTrace_append hprefix tailTrace_7307341
  have hstable : (prefixWord ++ tailWord_7307341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307341).length < 2 ^ (prefixWord ++ tailWord_7307341).sum := by decide
  have hdescent : baseEnd_7307341 < baseStart_7307341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307363 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7307363 : Nat := 118140960795 + 7307363 * 2 ^ 59
def prefixEnd_7307363 : Nat := 4983230072969 + 3 ^ 40 * 7307363 * 2
def baseEnd_7307363 : Nat := 3752189535880598642356555

theorem tailTrace_7307363 : CollatzResearch.WordTrace tailWord_7307363 prefixEnd_7307363 3752189535880598642356555 := by
  unfold tailWord_7307363
  simp only [CollatzResearch.WordTrace]
  refine ⟨266521424225679324087294743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177680949483786216058196495 266521424225679324087294743)
  ·
    refine ⟨399782136338518986130942115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266521424225679324087294743 399782136338518986130942115)
    ·
      refine ⟨599673204507778479196413173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399782136338518986130942115 599673204507778479196413173)
      ·
        refine ⟨56219362922604232424663735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 599673204507778479196413173 56219362922604232424663735)
        ·
          refine ⟨84329044383906348636995603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56219362922604232424663735 84329044383906348636995603)
          ·
            refine ⟨126493566575859522955493405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84329044383906348636995603 126493566575859522955493405)
            ·
              refine ⟨47435087465947321108310027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126493566575859522955493405 47435087465947321108310027)
              ·
                refine ⟨71152631198920981662465041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47435087465947321108310027 71152631198920981662465041)
                ·
                  refine ⟨53364473399190736246848781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71152631198920981662465041 53364473399190736246848781)
                  ·
                    refine ⟨20011677524696526092568293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53364473399190736246848781 20011677524696526092568293)
                    ·
                      refine ⟨3752189535880598642356555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20011677524696526092568293 3752189535880598642356555)
                      ·
                        rfl

theorem cell23_7307363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7307363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307363 prefixEnd_7307363 := by exact prefixLift 7307363
  have htrace : WordTrace (prefixWord ++ tailWord_7307363) baseStart_7307363 baseEnd_7307363 := by
    simpa [prefixWord, tailWord_7307363, baseEnd_7307363] using wordTrace_append hprefix tailTrace_7307363
  have hstable : (prefixWord ++ tailWord_7307363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307363).length < 2 ^ (prefixWord ++ tailWord_7307363).sum := by decide
  have hdescent : baseEnd_7307363 < baseStart_7307363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307397 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_7307397 : Nat := 118140960795 + 7307397 * 2 ^ 59
def prefixEnd_7307397 : Nat := 4983230072969 + 3 ^ 40 * 7307397 * 2
def baseEnd_7307397 : Nat := 3752206994222851509331399

theorem tailTrace_7307397 : CollatzResearch.WordTrace tailWord_7307397 prefixEnd_7307397 3752206994222851509331399 := by
  unfold tailWord_7307397
  simp only [CollatzResearch.WordTrace]
  refine ⟨266522664307556147894032445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177681776205037431929354963 266522664307556147894032445)
  ·
    refine ⟨99945999115333555460262167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266522664307556147894032445 99945999115333555460262167)
    ·
      refine ⟨149918998673000333190393251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99945999115333555460262167 149918998673000333190393251)
      ·
        refine ⟨224878498009500499785589877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149918998673000333190393251 224878498009500499785589877)
        ·
          refine ⟨21082359188390671854899051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224878498009500499785589877 21082359188390671854899051)
          ·
            refine ⟨31623538782586007782348577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082359188390671854899051 31623538782586007782348577)
            ·
              refine ⟨23717654086939505836761433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31623538782586007782348577 23717654086939505836761433)
              ·
                refine ⟨17788240565204629377571075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23717654086939505836761433 17788240565204629377571075)
                ·
                  refine ⟨26682360847806944066356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788240565204629377571075 26682360847806944066356613)
                  ·
                    refine ⟨5002942658963802012441865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26682360847806944066356613 5002942658963802012441865)
                    ·
                      refine ⟨3752206994222851509331399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002942658963802012441865 3752206994222851509331399)
                      ·
                        rfl

theorem cell23_7307397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_7307397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307397 prefixEnd_7307397 := by exact prefixLift 7307397
  have htrace : WordTrace (prefixWord ++ tailWord_7307397) baseStart_7307397 baseEnd_7307397 := by
    simpa [prefixWord, tailWord_7307397, baseEnd_7307397] using wordTrace_append hprefix tailTrace_7307397
  have hstable : (prefixWord ++ tailWord_7307397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307397).length < 2 ^ (prefixWord ++ tailWord_7307397).sum := by decide
  have hdescent : baseEnd_7307397 < baseStart_7307397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307410 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7307410 : Nat := 118140960795 + 7307410 * 2 ^ 59
def prefixEnd_7307410 : Nat := 4983230072969 + 3 ^ 40 * 7307410 * 2
def baseEnd_7307410 : Nat := 3752213669471359958468839

theorem tailTrace_7307410 : CollatzResearch.WordTrace tailWord_7307410 prefixEnd_7307410 3752213669471359958468839 := by
  unfold tailWord_7307410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66630784614127262778563921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177682092304339367409503789 66630784614127262778563921)
  ·
    refine ⟨49973088460595447083922941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66630784614127262778563921 49973088460595447083922941)
    ·
      refine ⟨18739908172723292656471103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49973088460595447083922941 18739908172723292656471103)
      ·
        refine ⟨28109862259084938984706655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18739908172723292656471103 28109862259084938984706655)
        ·
          refine ⟨42164793388627408477059983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28109862259084938984706655 42164793388627408477059983)
          ·
            refine ⟨63247190082941112715589975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42164793388627408477059983 63247190082941112715589975)
            ·
              refine ⟨94870785124411669073384963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63247190082941112715589975 94870785124411669073384963)
              ·
                refine ⟨142306177686617503610077445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94870785124411669073384963 142306177686617503610077445)
                ·
                  refine ⟨26682408316240781926889521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142306177686617503610077445 26682408316240781926889521)
                  ·
                    refine ⟨20011806237180586445167141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26682408316240781926889521 20011806237180586445167141)
                    ·
                      refine ⟨3752213669471359958468839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20011806237180586445167141 3752213669471359958468839)
                      ·
                        rfl

theorem cell23_7307410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7307410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307410 prefixEnd_7307410 := by exact prefixLift 7307410
  have htrace : WordTrace (prefixWord ++ tailWord_7307410) baseStart_7307410 baseEnd_7307410 := by
    simpa [prefixWord, tailWord_7307410, baseEnd_7307410] using wordTrace_append hprefix tailTrace_7307410
  have hstable : (prefixWord ++ tailWord_7307410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307410).length < 2 ^ (prefixWord ++ tailWord_7307410).sum := by decide
  have hdescent : baseEnd_7307410 < baseStart_7307410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307420 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 7]
def baseStart_7307420 : Nat := 118140960795 + 7307420 * 2 ^ 59
def prefixEnd_7307420 : Nat := 4983230072969 + 3 ^ 40 * 7307420 * 2
def baseEnd_7307420 : Nat := 416913200475322768815977

theorem tailTrace_7307420 : CollatzResearch.WordTrace tailWord_7307420 prefixEnd_7307420 416913200475322768815977 := by
  unfold tailWord_7307420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133261751593236411411059857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177682335457648548548079809 133261751593236411411059857)
  ·
    refine ⟨99946313694927308558294893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133261751593236411411059857 99946313694927308558294893)
    ·
      refine ⟨37479867635597740709360585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99946313694927308558294893 37479867635597740709360585)
      ·
        refine ⟨28109900726698305532020439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37479867635597740709360585 28109900726698305532020439)
        ·
          refine ⟨42164851090047458298030659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28109900726698305532020439 42164851090047458298030659)
          ·
            refine ⟨63247276635071187447045989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42164851090047458298030659 63247276635071187447045989)
            ·
              refine ⟨11858864369075847646321123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63247276635071187447045989 11858864369075847646321123)
              ·
                refine ⟨17788296553613771469481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11858864369075847646321123 17788296553613771469481685)
                ·
                  refine ⟨416913200475322768815977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17788296553613771469481685 416913200475322768815977)
                  ·
                    rfl

theorem cell23_7307420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_7307420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307420 prefixEnd_7307420 := by exact prefixLift 7307420
  have htrace : WordTrace (prefixWord ++ tailWord_7307420) baseStart_7307420 baseEnd_7307420 := by
    simpa [prefixWord, tailWord_7307420, baseEnd_7307420] using wordTrace_append hprefix tailTrace_7307420
  have hstable : (prefixWord ++ tailWord_7307420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307420).length < 2 ^ (prefixWord ++ tailWord_7307420).sum := by decide
  have hdescent : baseEnd_7307420 < baseStart_7307420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307431 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7307431 : Nat := 118140960795 + 7307431 * 2 ^ 59
def prefixEnd_7307431 : Nat := 4983230072969 + 3 ^ 40 * 7307431 * 2
def baseEnd_7307431 : Nat := 3752224452565104376306243

theorem tailTrace_7307431 : CollatzResearch.WordTrace tailWord_7307431 prefixEnd_7307431 3752224452565104376306243 := by
  unfold tailWord_7307431
  simp only [CollatzResearch.WordTrace]
  refine ⟨266523904389432971700770147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177682602926288647800513431 266523904389432971700770147)
  ·
    refine ⟨399785856584149457551155221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266523904389432971700770147 399785856584149457551155221)
    ·
      refine ⟨18739962027382005822710401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 399785856584149457551155221 18739962027382005822710401)
      ·
        refine ⟨14054971520536504367032801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18739962027382005822710401 14054971520536504367032801)
        ·
          refine ⟨10541228640402378275274601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14054971520536504367032801 10541228640402378275274601)
          ·
            refine ⟨7905921480301783706455951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10541228640402378275274601 7905921480301783706455951)
            ·
              refine ⟨11858882220452675559683927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905921480301783706455951 11858882220452675559683927)
              ·
                refine ⟨17788323330679013339525891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11858882220452675559683927 17788323330679013339525891)
                ·
                  refine ⟨26682484996018520009288837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788323330679013339525891 26682484996018520009288837)
                  ·
                    refine ⟨5002965936753472501741657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26682484996018520009288837 5002965936753472501741657)
                    ·
                      refine ⟨3752224452565104376306243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5002965936753472501741657 3752224452565104376306243)
                      ·
                        rfl

theorem cell23_7307431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7307431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307431 prefixEnd_7307431 := by exact prefixLift 7307431
  have htrace : WordTrace (prefixWord ++ tailWord_7307431) baseStart_7307431 baseEnd_7307431 := by
    simpa [prefixWord, tailWord_7307431, baseEnd_7307431] using wordTrace_append hprefix tailTrace_7307431
  have hstable : (prefixWord ++ tailWord_7307431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307431).length < 2 ^ (prefixWord ++ tailWord_7307431).sum := by decide
  have hdescent : baseEnd_7307431 < baseStart_7307431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307443 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_7307443 : Nat := 118140960795 + 7307443 * 2 ^ 59
def prefixEnd_7307443 : Nat := 4983230072969 + 3 ^ 40 * 7307443 * 2
def baseEnd_7307443 : Nat := 3752230614332958329356187

theorem tailTrace_7307443 : CollatzResearch.WordTrace tailWord_7307443 prefixEnd_7307443 3752230614332958329356187 := by
  unfold tailWord_7307443
  simp only [CollatzResearch.WordTrace]
  refine ⟨266524342065389497750206983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177682894710259665166804655 266524342065389497750206983)
  ·
    refine ⟨399786513098084246625310475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266524342065389497750206983 399786513098084246625310475)
    ·
      refine ⟨599679769647126369937965713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399786513098084246625310475 599679769647126369937965713)
      ·
        refine ⟨449759827235344777453474285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599679769647126369937965713 449759827235344777453474285)
        ·
          refine ⟨168659935213254291545052857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449759827235344777453474285 168659935213254291545052857)
          ·
            refine ⟨126494951409940718658789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168659935213254291545052857 126494951409940718658789643)
            ·
              refine ⟨189742427114911077988184465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126494951409940718658789643 189742427114911077988184465)
              ·
                refine ⟨142306820336183308491138349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189742427114911077988184465 142306820336183308491138349)
                ·
                  refine ⟨53365057626068740684176881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142306820336183308491138349 53365057626068740684176881)
                  ·
                    refine ⟨40023793219551555513132661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53365057626068740684176881 40023793219551555513132661)
                    ·
                      refine ⟨3752230614332958329356187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40023793219551555513132661 3752230614332958329356187)
                      ·
                        rfl

theorem cell23_7307443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_7307443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307443 prefixEnd_7307443 := by exact prefixLift 7307443
  have htrace : WordTrace (prefixWord ++ tailWord_7307443) baseStart_7307443 baseEnd_7307443 := by
    simpa [prefixWord, tailWord_7307443, baseEnd_7307443] using wordTrace_append hprefix tailTrace_7307443
  have hstable : (prefixWord ++ tailWord_7307443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307443).length < 2 ^ (prefixWord ++ tailWord_7307443).sum := by decide
  have hdescent : baseEnd_7307443 < baseStart_7307443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307477 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7307477 : Nat := 118140960795 + 7307477 * 2 ^ 59
def prefixEnd_7307477 : Nat := 4983230072969 + 3 ^ 40 * 7307477 * 2
def baseEnd_7307477 : Nat := 3752248072675211196331031

theorem tailTrace_7307477 : CollatzResearch.WordTrace tailWord_7307477 prefixEnd_7307477 3752248072675211196331031 := by
  unfold tailWord_7307477
  simp only [CollatzResearch.WordTrace]
  refine ⟨266525582147266321556944685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177683721431510881037963123 266525582147266321556944685)
  ·
    refine ⟨99947093305224870583854257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266525582147266321556944685 99947093305224870583854257)
    ·
      refine ⟨74960319978918652937890693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99947093305224870583854257 74960319978918652937890693)
      ·
        refine ⟨14055059996047247425854505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74960319978918652937890693 14055059996047247425854505)
        ·
          refine ⟨10541294997035435569390879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14055059996047247425854505 10541294997035435569390879)
          ·
            refine ⟨15811942495553153354086319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541294997035435569390879 15811942495553153354086319)
            ·
              refine ⟨23717913743329730031129479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15811942495553153354086319 23717913743329730031129479)
              ·
                refine ⟨35576870614994595046694219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23717913743329730031129479 35576870614994595046694219)
                ·
                  refine ⟨53365305922491892570041329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35576870614994595046694219 53365305922491892570041329)
                  ·
                    refine ⟨40023979441868919427530997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53365305922491892570041329 40023979441868919427530997)
                    ·
                      refine ⟨3752248072675211196331031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40023979441868919427530997 3752248072675211196331031)
                      ·
                        rfl

theorem cell23_7307477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7307477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307477 prefixEnd_7307477 := by exact prefixLift 7307477
  have htrace : WordTrace (prefixWord ++ tailWord_7307477) baseStart_7307477 baseEnd_7307477 := by
    simpa [prefixWord, tailWord_7307477, baseEnd_7307477] using wordTrace_append hprefix tailTrace_7307477
  have hstable : (prefixWord ++ tailWord_7307477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307477).length < 2 ^ (prefixWord ++ tailWord_7307477).sum := by decide
  have hdescent : baseEnd_7307477 < baseStart_7307477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_7307483 : Nat := 118140960795 + 7307483 * 2 ^ 59
def prefixEnd_7307483 : Nat := 4983230072969 + 3 ^ 40 * 7307483 * 2
def baseEnd_7307483 : Nat := 3752251153559138172856003

theorem tailTrace_7307483 : CollatzResearch.WordTrace tailWord_7307483 prefixEnd_7307483 3752251153559138172856003 := by
  unfold tailWord_7307483
  simp only [CollatzResearch.WordTrace]
  refine ⟨266525800985244584581663103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177683867323496389721108735 266525800985244584581663103)
  ·
    refine ⟨399788701477866876872494655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266525800985244584581663103 399788701477866876872494655)
    ·
      refine ⟨599683052216800315308741983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399788701477866876872494655 599683052216800315308741983)
      ·
        refine ⟨899524578325200472963112975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599683052216800315308741983 899524578325200472963112975)
        ·
          refine ⟨1349286867487800709444669463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899524578325200472963112975 1349286867487800709444669463)
          ·
            refine ⟨2023930301231701064167004195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349286867487800709444669463 2023930301231701064167004195)
            ·
              refine ⟨3035895451847551596250506293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023930301231701064167004195 3035895451847551596250506293)
              ·
                refine ⟨284615198610707962148484965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3035895451847551596250506293 284615198610707962148484965)
                ·
                  refine ⟨53365349739507742902840931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284615198610707962148484965 53365349739507742902840931)
                  ·
                    refine ⟨80048024609261614354261397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53365349739507742902840931 80048024609261614354261397)
                    ·
                      refine ⟨3752251153559138172856003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80048024609261614354261397 3752251153559138172856003)
                      ·
                        rfl

theorem cell23_7307483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_7307483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307483 prefixEnd_7307483 := by exact prefixLift 7307483
  have htrace : WordTrace (prefixWord ++ tailWord_7307483) baseStart_7307483 baseEnd_7307483 := by
    simpa [prefixWord, tailWord_7307483, baseEnd_7307483] using wordTrace_append hprefix tailTrace_7307483
  have hstable : (prefixWord ++ tailWord_7307483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307483).length < 2 ^ (prefixWord ++ tailWord_7307483).sum := by decide
  have hdescent : baseEnd_7307483 < baseStart_7307483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307507 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3]
def baseStart_7307507 : Nat := 118140960795 + 7307507 * 2 ^ 59
def prefixEnd_7307507 : Nat := 4983230072969 + 3 ^ 40 * 7307507 * 2
def baseEnd_7307507 : Nat := 3752263477094846078955893

theorem tailTrace_7307507 : CollatzResearch.WordTrace tailWord_7307507 prefixEnd_7307507 3752263477094846078955893 := by
  unfold tailWord_7307507
  simp only [CollatzResearch.WordTrace]
  refine ⟨266526676337157636680536775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177684450891438424453691183 266526676337157636680536775)
  ·
    refine ⟨399790014505736455020805163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266526676337157636680536775 399790014505736455020805163)
    ·
      refine ⟨599685021758604682531207745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399790014505736455020805163 599685021758604682531207745)
      ·
        refine ⟨449763766318953511898405809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599685021758604682531207745 449763766318953511898405809)
        ·
          refine ⟨337322824739215133923804357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449763766318953511898405809 337322824739215133923804357)
          ·
            refine ⟨63248029638602837610713317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337322824739215133923804357 63248029638602837610713317)
            ·
              refine ⟨11859005557238032052008747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63248029638602837610713317 11859005557238032052008747)
              ·
                refine ⟨17788508335857048078013121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859005557238032052008747 17788508335857048078013121)
                ·
                  refine ⟨13341381251892786058509841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17788508335857048078013121 13341381251892786058509841)
                  ·
                    refine ⟨10006035938919589543882381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13341381251892786058509841 10006035938919589543882381)
                    ·
                      refine ⟨3752263477094846078955893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006035938919589543882381 3752263477094846078955893)
                      ·
                        rfl

theorem cell23_7307507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_7307507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307507 prefixEnd_7307507 := by exact prefixLift 7307507
  have htrace : WordTrace (prefixWord ++ tailWord_7307507) baseStart_7307507 baseEnd_7307507 := by
    simpa [prefixWord, tailWord_7307507, baseEnd_7307507] using wordTrace_append hprefix tailTrace_7307507
  have hstable : (prefixWord ++ tailWord_7307507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307507).length < 2 ^ (prefixWord ++ tailWord_7307507).sum := by decide
  have hdescent : baseEnd_7307507 < baseStart_7307507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307510 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7307510 : Nat := 118140960795 + 7307510 * 2 ^ 59
def prefixEnd_7307510 : Nat := 4983230072969 + 3 ^ 40 * 7307510 * 2
def baseEnd_7307510 : Nat := 416918335281867729690931

theorem tailTrace_7307510 : CollatzResearch.WordTrace tailWord_7307510 prefixEnd_7307510 416918335281867729690931 := by
  unfold tailWord_7307510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657924109759173012055999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177684523837431178795263989 16657924109759173012055999)
  ·
    refine ⟨24986886164638759518083999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16657924109759173012055999 24986886164638759518083999)
    ·
      refine ⟨37480329246958139277125999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24986886164638759518083999 37480329246958139277125999)
      ·
        refine ⟨56220493870437208915688999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37480329246958139277125999 56220493870437208915688999)
        ·
          refine ⟨84330740805655813373533499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56220493870437208915688999 84330740805655813373533499)
          ·
            refine ⟨126496111208483720060300249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84330740805655813373533499 126496111208483720060300249)
            ·
              refine ⟨94872083406362790045225187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126496111208483720060300249 94872083406362790045225187)
              ·
                refine ⟨142308125109544185067837781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94872083406362790045225187 142308125109544185067837781)
                ·
                  refine ⟨416918335281867729690931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142308125109544185067837781 416918335281867729690931)
                  ·
                    rfl

theorem cell23_7307510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7307510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307510 prefixEnd_7307510 := by exact prefixLift 7307510
  have htrace : WordTrace (prefixWord ++ tailWord_7307510) baseStart_7307510 baseEnd_7307510 := by
    simpa [prefixWord, tailWord_7307510, baseEnd_7307510] using wordTrace_append hprefix tailTrace_7307510
  have hstable : (prefixWord ++ tailWord_7307510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307510).length < 2 ^ (prefixWord ++ tailWord_7307510).sum := by decide
  have hdescent : baseEnd_7307510 < baseStart_7307510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307547 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 4, 3, 2]
def baseStart_7307547 : Nat := 118140960795 + 7307547 * 2 ^ 59
def prefixEnd_7307547 : Nat := 4983230072969 + 3 ^ 40 * 7307547 * 2
def baseEnd_7307547 : Nat := 3752284016321025922455709

theorem tailTrace_7307547 : CollatzResearch.WordTrace tailWord_7307547 prefixEnd_7307547 3752284016321025922455709 := by
  unfold tailWord_7307547
  simp only [CollatzResearch.WordTrace]
  refine ⟨266528135257012723511992895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177685423504675149007995263 266528135257012723511992895)
  ·
    refine ⟨399792202885519085267989343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266528135257012723511992895 399792202885519085267989343)
    ·
      refine ⟨599688304328278627901984015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399792202885519085267989343 599688304328278627901984015)
      ·
        refine ⟨899532456492417941852976023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599688304328278627901984015 899532456492417941852976023)
        ·
          refine ⟨1349298684738626912779464035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899532456492417941852976023 1349298684738626912779464035)
          ·
            refine ⟨2023948027107940369169196053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349298684738626912779464035 2023948027107940369169196053)
            ·
              refine ⟨94872563770684704804806065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2023948027107940369169196053 94872563770684704804806065)
              ·
                refine ⟨71154422828013528603604549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94872563770684704804806065 71154422828013528603604549)
                ·
                  refine ⟨13341454280252536613175853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71154422828013528603604549 13341454280252536613175853)
                  ·
                    refine ⟨5003045355094701229940945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13341454280252536613175853 5003045355094701229940945)
                    ·
                      refine ⟨3752284016321025922455709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003045355094701229940945 3752284016321025922455709)
                      ·
                        rfl

theorem cell23_7307547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3, 2].length) (baseStart_7307547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307547 prefixEnd_7307547 := by exact prefixLift 7307547
  have htrace : WordTrace (prefixWord ++ tailWord_7307547) baseStart_7307547 baseEnd_7307547 := by
    simpa [prefixWord, tailWord_7307547, baseEnd_7307547] using wordTrace_append hprefix tailTrace_7307547
  have hstable : (prefixWord ++ tailWord_7307547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307547).length < 2 ^ (prefixWord ++ tailWord_7307547).sum := by decide
  have hdescent : baseEnd_7307547 < baseStart_7307547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307554 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_7307554 : Nat := 118140960795 + 7307554 * 2 ^ 59
def prefixEnd_7307554 : Nat := 4983230072969 + 3 ^ 40 * 7307554 * 2
def baseEnd_7307554 : Nat := 3752287610685607395068177

theorem tailTrace_7307554 : CollatzResearch.WordTrace tailWord_7307554 prefixEnd_7307554 3752287610685607395068177 := by
  unfold tailWord_7307554
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632097641996840926874429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177685593711991575804998477 66632097641996840926874429)
  ·
    refine ⟨24987036615748815347577911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66632097641996840926874429 24987036615748815347577911)
    ·
      refine ⟨37480554923623223021366867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24987036615748815347577911 37480554923623223021366867)
      ·
        refine ⟨56220832385434834532050301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37480554923623223021366867 56220832385434834532050301)
        ·
          refine ⟨21082812144538062949518863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56220832385434834532050301 21082812144538062949518863)
          ·
            refine ⟨31624218216807094424278295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082812144538062949518863 31624218216807094424278295)
            ·
              refine ⟨47436327325210641636417443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31624218216807094424278295 47436327325210641636417443)
              ·
                refine ⟨71154490987815962454626165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47436327325210641636417443 71154490987815962454626165)
                ·
                  refine ⟨6670733530107746480121203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71154490987815962454626165 6670733530107746480121203)
                  ·
                    refine ⟨10006100295161619720181805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670733530107746480121203 10006100295161619720181805)
                    ·
                      refine ⟨3752287610685607395068177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006100295161619720181805 3752287610685607395068177)
                      ·
                        rfl

theorem cell23_7307554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_7307554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307554 prefixEnd_7307554 := by exact prefixLift 7307554
  have htrace : WordTrace (prefixWord ++ tailWord_7307554) baseStart_7307554 baseEnd_7307554 := by
    simpa [prefixWord, tailWord_7307554, baseEnd_7307554] using wordTrace_append hprefix tailTrace_7307554
  have hstable : (prefixWord ++ tailWord_7307554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307554).length < 2 ^ (prefixWord ++ tailWord_7307554).sum := by decide
  have hdescent : baseEnd_7307554 < baseStart_7307554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307564 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_7307564 : Nat := 118140960795 + 7307564 * 2 ^ 59
def prefixEnd_7307564 : Nat := 4983230072969 + 3 ^ 40 * 7307564 * 2
def baseEnd_7307564 : Nat := 3752292745492152355943131

theorem tailTrace_7307564 : CollatzResearch.WordTrace tailWord_7307564 prefixEnd_7307564 3752292745492152355943131 := by
  unfold tailWord_7307564
  simp only [CollatzResearch.WordTrace]
  refine ⟨133264377648975567707680873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177685836865300756943574497 133264377648975567707680873)
  ·
    refine ⟨99948283236731675780760655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133264377648975567707680873 99948283236731675780760655)
    ·
      refine ⟨149922424855097513671140983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99948283236731675780760655 149922424855097513671140983)
      ·
        refine ⟨224883637282646270506711475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149922424855097513671140983 224883637282646270506711475)
        ·
          refine ⟨337325455923969405760067213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224883637282646270506711475 337325455923969405760067213)
          ·
            refine ⟨126497045971488527160025205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337325455923969405760067213 126497045971488527160025205)
            ·
              refine ⟨11859098059827049421252363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126497045971488527160025205 11859098059827049421252363)
              ·
                refine ⟨17788647089740574131878545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859098059827049421252363 17788647089740574131878545)
                ·
                  refine ⟨13341485317305430598908909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17788647089740574131878545 13341485317305430598908909)
                  ·
                    refine ⟨5003056993989536474590841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13341485317305430598908909 5003056993989536474590841)
                    ·
                      refine ⟨3752292745492152355943131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003056993989536474590841 3752292745492152355943131)
                      ·
                        rfl

theorem cell23_7307564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_7307564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307564 prefixEnd_7307564 := by exact prefixLift 7307564
  have htrace : WordTrace (prefixWord ++ tailWord_7307564) baseStart_7307564 baseEnd_7307564 := by
    simpa [prefixWord, tailWord_7307564, baseEnd_7307564] using wordTrace_append hprefix tailTrace_7307564
  have hstable : (prefixWord ++ tailWord_7307564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307564).length < 2 ^ (prefixWord ++ tailWord_7307564).sum := by decide
  have hdescent : baseEnd_7307564 < baseStart_7307564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307571 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 1, 1, 3]
def baseStart_7307571 : Nat := 118140960795 + 7307571 * 2 ^ 59
def prefixEnd_7307571 : Nat := 4983230072969 + 3 ^ 40 * 7307571 * 2
def baseEnd_7307571 : Nat := 3752296339856733828555599

theorem tailTrace_7307571 : CollatzResearch.WordTrace tailWord_7307571 prefixEnd_7307571 3752296339856733828555599 := by
  unfold tailWord_7307571
  simp only [CollatzResearch.WordTrace]
  refine ⟨266529010608925775610866567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177686007072617183740577711 266529010608925775610866567)
  ·
    refine ⟨399793515913388663416299851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266529010608925775610866567 399793515913388663416299851)
    ·
      refine ⟨599690273870082995124449777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399793515913388663416299851 599690273870082995124449777)
      ·
        refine ⟨449767705402562246343337333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599690273870082995124449777 449767705402562246343337333)
        ·
          refine ⟨42165722381490210594687875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 449767705402562246343337333 42165722381490210594687875)
          ·
            refine ⟨63248583572235315892031813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42165722381490210594687875 63248583572235315892031813)
            ·
              refine ⟨11859109419794121729755965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63248583572235315892031813 11859109419794121729755965)
              ·
                refine ⟨4447166032422795648658487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11859109419794121729755965 4447166032422795648658487)
                ·
                  refine ⟨6670749048634193472987731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447166032422795648658487 6670749048634193472987731)
                  ·
                    refine ⟨10006123572951290209481597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670749048634193472987731 10006123572951290209481597)
                    ·
                      refine ⟨3752296339856733828555599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006123572951290209481597 3752296339856733828555599)
                      ·
                        rfl

theorem cell23_7307571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 1, 3].length) (baseStart_7307571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307571 prefixEnd_7307571 := by exact prefixLift 7307571
  have htrace : WordTrace (prefixWord ++ tailWord_7307571) baseStart_7307571 baseEnd_7307571 := by
    simpa [prefixWord, tailWord_7307571, baseEnd_7307571] using wordTrace_append hprefix tailTrace_7307571
  have hstable : (prefixWord ++ tailWord_7307571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307571).length < 2 ^ (prefixWord ++ tailWord_7307571).sum := by decide
  have hdescent : baseEnd_7307571 < baseStart_7307571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307588 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7307588 : Nat := 118140960795 + 7307588 * 2 ^ 59
def prefixEnd_7307588 : Nat := 4983230072969 + 3 ^ 40 * 7307588 * 2
def baseEnd_7307588 : Nat := 3752305069027860262043021

theorem tailTrace_7307588 : CollatzResearch.WordTrace tailWord_7307588 prefixEnd_7307588 3752305069027860262043021 := by
  unfold tailWord_7307588
  simp only [CollatzResearch.WordTrace]
  refine ⟨133264815324932093757117709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177686420433242791676156945 133264815324932093757117709)
  ·
    refine ⟨49974305746849535158919141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133264815324932093757117709 49974305746849535158919141)
    ·
      refine ⟨9370182327534287842297339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49974305746849535158919141 9370182327534287842297339)
      ·
        refine ⟨14055273491301431763446009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370182327534287842297339 14055273491301431763446009)
        ·
          refine ⟨10541455118476073822584507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14055273491301431763446009 10541455118476073822584507)
          ·
            refine ⟨15812182677714110733876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541455118476073822584507 15812182677714110733876761)
            ·
              refine ⟨11859137008285583050407571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812182677714110733876761 11859137008285583050407571)
              ·
                refine ⟨17788705512428374575611357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859137008285583050407571 17788705512428374575611357)
                ·
                  refine ⟨6670764567160640465854259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17788705512428374575611357 6670764567160640465854259)
                  ·
                    refine ⟨10006146850740960698781389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670764567160640465854259 10006146850740960698781389)
                    ·
                      refine ⟨3752305069027860262043021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006146850740960698781389 3752305069027860262043021)
                      ·
                        rfl

theorem cell23_7307588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7307588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307588 prefixEnd_7307588 := by exact prefixLift 7307588
  have htrace : WordTrace (prefixWord ++ tailWord_7307588) baseStart_7307588 baseEnd_7307588 := by
    simpa [prefixWord, tailWord_7307588, baseEnd_7307588] using wordTrace_append hprefix tailTrace_7307588
  have hstable : (prefixWord ++ tailWord_7307588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307588).length < 2 ^ (prefixWord ++ tailWord_7307588).sum := by decide
  have hdescent : baseEnd_7307588 < baseStart_7307588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307604 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_7307604 : Nat := 118140960795 + 7307604 * 2 ^ 59
def prefixEnd_7307604 : Nat := 4983230072969 + 3 ^ 40 * 7307604 * 2
def baseEnd_7307604 : Nat := 1250771094906110733147649

theorem tailTrace_7307604 : CollatzResearch.WordTrace tailWord_7307604 prefixEnd_7307604 1250771094906110733147649 := by
  unfold tailWord_7307604
  simp only [CollatzResearch.WordTrace]
  refine ⟨133265107108903111123408933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177686809478537481497878577 133265107108903111123408933)
  ·
    refine ⟨24987207582919333335639175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133265107108903111123408933 24987207582919333335639175)
    ·
      refine ⟨37480811374379000003458763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24987207582919333335639175 37480811374379000003458763)
      ·
        refine ⟨56221217061568500005188145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37480811374379000003458763 56221217061568500005188145)
        ·
          refine ⟨42165912796176375003891109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56221217061568500005188145 42165912796176375003891109)
          ·
            refine ⟨7906108649283070313229583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42165912796176375003891109 7906108649283070313229583)
            ·
              refine ⟨11859162973924605469844375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906108649283070313229583 11859162973924605469844375)
              ·
                refine ⟨17788744460886908204766563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859162973924605469844375 17788744460886908204766563)
                ·
                  refine ⟨26683116691330362307149845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788744460886908204766563 26683116691330362307149845)
                  ·
                    refine ⟨1250771094906110733147649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26683116691330362307149845 1250771094906110733147649)
                    ·
                      rfl

theorem cell23_7307604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_7307604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307604 prefixEnd_7307604 := by exact prefixLift 7307604
  have htrace : WordTrace (prefixWord ++ tailWord_7307604) baseStart_7307604 baseEnd_7307604 := by
    simpa [prefixWord, tailWord_7307604, baseEnd_7307604] using wordTrace_append hprefix tailTrace_7307604
  have hstable : (prefixWord ++ tailWord_7307604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307604).length < 2 ^ (prefixWord ++ tailWord_7307604).sum := by decide
  have hdescent : baseEnd_7307604 < baseStart_7307604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307645 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_7307645 : Nat := 118140960795 + 7307645 * 2 ^ 59
def prefixEnd_7307645 : Nat := 4983230072969 + 3 ^ 40 * 7307645 * 2
def baseEnd_7307645 : Nat := 3752334337425166539030259

theorem tailTrace_7307645 : CollatzResearch.WordTrace tailWord_7307645 prefixEnd_7307645 3752334337425166539030259 := by
  unfold tailWord_7307645
  simp only [CollatzResearch.WordTrace]
  refine ⟨266531709610657686249060389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177687806407105124166040259 266531709610657686249060389)
  ·
    refine ⟨49974695551998316171698823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266531709610657686249060389 49974695551998316171698823)
    ·
      refine ⟨74962043327997474257548235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49974695551998316171698823 74962043327997474257548235)
      ·
        refine ⟨112443064991996211386322353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74962043327997474257548235 112443064991996211386322353)
        ·
          refine ⟨84332298743997158539741765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112443064991996211386322353 84332298743997158539741765)
          ·
            refine ⟨15812306014499467226201581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84332298743997158539741765 15812306014499467226201581)
            ·
              refine ⟨5929614755437300209825593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15812306014499467226201581 5929614755437300209825593)
              ·
                refine ⟨4447211066577975157369195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5929614755437300209825593 4447211066577975157369195)
                ·
                  refine ⟨6670816599866962736053793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447211066577975157369195 6670816599866962736053793)
                  ·
                    refine ⟨5003112449900222052040345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670816599866962736053793 5003112449900222052040345)
                    ·
                      refine ⟨3752334337425166539030259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003112449900222052040345 3752334337425166539030259)
                      ·
                        rfl

theorem cell23_7307645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_7307645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307645 prefixEnd_7307645 := by exact prefixLift 7307645
  have htrace : WordTrace (prefixWord ++ tailWord_7307645) baseStart_7307645 baseEnd_7307645 := by
    simpa [prefixWord, tailWord_7307645, baseEnd_7307645] using wordTrace_append hprefix tailTrace_7307645
  have hstable : (prefixWord ++ tailWord_7307645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307645).length < 2 ^ (prefixWord ++ tailWord_7307645).sum := by decide
  have hdescent : baseEnd_7307645 < baseStart_7307645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307671 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_7307671 : Nat := 118140960795 + 7307671 * 2 ^ 59
def prefixEnd_7307671 : Nat := 4983230072969 + 3 ^ 40 * 7307671 * 2
def baseEnd_7307671 : Nat := 3752347687922183437305139

theorem tailTrace_7307671 : CollatzResearch.WordTrace tailWord_7307671 prefixEnd_7307671 3752347687922183437305139 := by
  unfold tailWord_7307671
  simp only [CollatzResearch.WordTrace]
  refine ⟨266532657908563492689506867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177688438605708995126337911 266532657908563492689506867)
  ·
    refine ⟨399798986862845239034260301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266532657908563492689506867 399798986862845239034260301)
    ·
      refine ⟨149924620073566964637847613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399798986862845239034260301 149924620073566964637847613)
      ·
        refine ⟨56221732527587611739192855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149924620073566964637847613 56221732527587611739192855)
        ·
          refine ⟨84332598791381417608789283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56221732527587611739192855 84332598791381417608789283)
          ·
            refine ⟨126498898187072126413183925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84332598791381417608789283 126498898187072126413183925)
            ·
              refine ⟨11859271705038011851235993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126498898187072126413183925 11859271705038011851235993)
              ·
                refine ⟨8894453778778508888426995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11859271705038011851235993 8894453778778508888426995)
                ·
                  refine ⟨13341680668167763332640493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8894453778778508888426995 13341680668167763332640493)
                  ·
                    refine ⟨5003130250562911249740185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13341680668167763332640493 5003130250562911249740185)
                    ·
                      refine ⟨3752347687922183437305139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003130250562911249740185 3752347687922183437305139)
                      ·
                        rfl

theorem cell23_7307671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_7307671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307671 prefixEnd_7307671 := by exact prefixLift 7307671
  have htrace : WordTrace (prefixWord ++ tailWord_7307671) baseStart_7307671 baseEnd_7307671 := by
    simpa [prefixWord, tailWord_7307671, baseEnd_7307671] using wordTrace_append hprefix tailTrace_7307671
  have hstable : (prefixWord ++ tailWord_7307671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307671).length < 2 ^ (prefixWord ++ tailWord_7307671).sum := by decide
  have hdescent : baseEnd_7307671 < baseStart_7307671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307684 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_7307684 : Nat := 118140960795 + 7307684 * 2 ^ 59
def prefixEnd_7307684 : Nat := 4983230072969 + 3 ^ 40 * 7307684 * 2
def baseEnd_7307684 : Nat := 3752354363170691886442579

theorem tailTrace_7307684 : CollatzResearch.WordTrace tailWord_7307684 prefixEnd_7307684 3752354363170691886442579 := by
  unfold tailWord_7307684
  simp only [CollatzResearch.WordTrace]
  refine ⟨133266566028758197954865053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177688754705010930606486737 133266566028758197954865053)
  ·
    refine ⟨49974962260784324233074395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133266566028758197954865053 49974962260784324233074395)
    ·
      refine ⟨74962443391176486349611593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49974962260784324233074395 74962443391176486349611593)
      ·
        refine ⟨56221832543382364762208695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74962443391176486349611593 56221832543382364762208695)
        ·
          refine ⟨84332748815073547143313043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56221832543382364762208695 84332748815073547143313043)
          ·
            refine ⟨126499123222610320714969565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84332748815073547143313043 126499123222610320714969565)
            ·
              refine ⟨47437171208478870268113587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126499123222610320714969565 47437171208478870268113587)
              ·
                refine ⟨71155756812718305402170381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47437171208478870268113587 71155756812718305402170381)
                ·
                  refine ⟨26683408804769364525813893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71155756812718305402170381 26683408804769364525813893)
                  ·
                    refine ⟨5003139150894255848590105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26683408804769364525813893 5003139150894255848590105)
                    ·
                      refine ⟨3752354363170691886442579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003139150894255848590105 3752354363170691886442579)
                      ·
                        rfl

theorem cell23_7307684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_7307684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307684 prefixEnd_7307684 := by exact prefixLift 7307684
  have htrace : WordTrace (prefixWord ++ tailWord_7307684) baseStart_7307684 baseEnd_7307684 := by
    simpa [prefixWord, tailWord_7307684, baseEnd_7307684] using wordTrace_append hprefix tailTrace_7307684
  have hstable : (prefixWord ++ tailWord_7307684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307684).length < 2 ^ (prefixWord ++ tailWord_7307684).sum := by decide
  have hdescent : baseEnd_7307684 < baseStart_7307684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307724 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 7]
def baseStart_7307724 : Nat := 118140960795 + 7307724 * 2 ^ 59
def prefixEnd_7307724 : Nat := 4983230072969 + 3 ^ 40 * 7307724 * 2
def baseEnd_7307724 : Nat := 416930544710763525549155

theorem tailTrace_7307724 : CollatzResearch.WordTrace tailWord_7307724 prefixEnd_7307724 416930544710763525549155 := by
  unfold tailWord_7307724
  simp only [CollatzResearch.WordTrace]
  refine ⟨133267295488685741370593113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177689727318247655160790817 133267295488685741370593113)
  ·
    refine ⟨99950471616514306027944835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133267295488685741370593113 99950471616514306027944835)
    ·
      refine ⟨149925707424771459041917253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99950471616514306027944835 149925707424771459041917253)
      ·
        refine ⟨28111070142144648570359485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149925707424771459041917253 28111070142144648570359485)
        ·
          refine ⟨10541651303304243213884807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28111070142144648570359485 10541651303304243213884807)
          ·
            refine ⟨15812476954956364820827211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541651303304243213884807 15812476954956364820827211)
            ·
              refine ⟨23718715432434547231240817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15812476954956364820827211 23718715432434547231240817)
              ·
                refine ⟨17789036574325910423430613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23718715432434547231240817 17789036574325910423430613)
                ·
                  refine ⟨416930544710763525549155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17789036574325910423430613 416930544710763525549155)
                  ·
                    rfl

theorem cell23_7307724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_7307724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307724 prefixEnd_7307724 := by exact prefixLift 7307724
  have htrace : WordTrace (prefixWord ++ tailWord_7307724) baseStart_7307724 baseEnd_7307724 := by
    simpa [prefixWord, tailWord_7307724, baseEnd_7307724] using wordTrace_append hprefix tailTrace_7307724
  have hstable : (prefixWord ++ tailWord_7307724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307724).length < 2 ^ (prefixWord ++ tailWord_7307724).sum := by decide
  have hdescent : baseEnd_7307724 < baseStart_7307724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307737 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_7307737 : Nat := 118140960795 + 7307737 * 2 ^ 59
def prefixEnd_7307737 : Nat := 4983230072969 + 3 ^ 40 * 7307737 * 2
def baseEnd_7307737 : Nat := 1250793859215126726359945

theorem tailTrace_7307737 : CollatzResearch.WordTrace tailWord_7307737 prefixEnd_7307737 1250793859215126726359945 := by
  unfold tailWord_7307737
  simp only [CollatzResearch.WordTrace]
  refine ⟨266535065126324385961409465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177690043417549590640939643 266535065126324385961409465)
  ·
    refine ⟨199901298844743289471057099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266535065126324385961409465 199901298844743289471057099)
    ·
      refine ⟨299851948267114934206585649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199901298844743289471057099 299851948267114934206585649)
      ·
        refine ⟨224888961200336200654939237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299851948267114934206585649 224888961200336200654939237)
        ·
          refine ⟨42166680225063037622801107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224888961200336200654939237 42166680225063037622801107)
          ·
            refine ⟨63250020337594556434201661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42166680225063037622801107 63250020337594556434201661)
            ·
              refine ⟨23718757626597958662825623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63250020337594556434201661 23718757626597958662825623)
              ·
                refine ⟨35578136439896937994238435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23718757626597958662825623 35578136439896937994238435)
                ·
                  refine ⟨53367204659845406991357653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35578136439896937994238435 53367204659845406991357653)
                  ·
                    refine ⟨1250793859215126726359945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53367204659845406991357653 1250793859215126726359945)
                    ·
                      rfl

theorem cell23_7307737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_7307737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307737 prefixEnd_7307737 := by exact prefixLift 7307737
  have htrace : WordTrace (prefixWord ++ tailWord_7307737) baseStart_7307737 baseEnd_7307737 := by
    simpa [prefixWord, tailWord_7307737, baseEnd_7307737] using wordTrace_append hprefix tailTrace_7307737
  have hstable : (prefixWord ++ tailWord_7307737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307737).length < 2 ^ (prefixWord ++ tailWord_7307737).sum := by decide
  have hdescent : baseEnd_7307737 < baseStart_7307737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307741 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 5]
def baseStart_7307741 : Nat := 118140960795 + 7307741 * 2 ^ 59
def prefixEnd_7307741 : Nat := 4983230072969 + 3 ^ 40 * 7307741 * 2
def baseEnd_7307741 : Nat := 416931514618666462603313

theorem tailTrace_7307741 : CollatzResearch.WordTrace tailWord_7307741 prefixEnd_7307741 416931514618666462603313 := by
  unfold tailWord_7307741
  simp only [CollatzResearch.WordTrace]
  refine ⟨266535211018309894644555077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177690140678873263096370051 266535211018309894644555077)
  ·
    refine ⟨49975352065933105245854077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266535211018309894644555077 49975352065933105245854077)
    ·
      refine ⟨18740757024724914467195279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49975352065933105245854077 18740757024724914467195279)
      ·
        refine ⟨28111135537087371700792919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18740757024724914467195279 28111135537087371700792919)
        ·
          refine ⟨42166703305631057551189379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111135537087371700792919 42166703305631057551189379)
          ·
            refine ⟨63250054958446586326784069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42166703305631057551189379 63250054958446586326784069)
            ·
              refine ⟨11859385304708734936272013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63250054958446586326784069 11859385304708734936272013)
              ·
                refine ⟨4447269489265775601102005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11859385304708734936272013 4447269489265775601102005)
                ·
                  refine ⟨416931514618666462603313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4447269489265775601102005 416931514618666462603313)
                  ·
                    rfl

theorem cell23_7307741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_7307741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307741 prefixEnd_7307741 := by exact prefixLift 7307741
  have htrace : WordTrace (prefixWord ++ tailWord_7307741) baseStart_7307741 baseEnd_7307741 := by
    simpa [prefixWord, tailWord_7307741, baseEnd_7307741] using wordTrace_append hprefix tailTrace_7307741
  have hstable : (prefixWord ++ tailWord_7307741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307741).length < 2 ^ (prefixWord ++ tailWord_7307741).sum := by decide
  have hdescent : baseEnd_7307741 < baseStart_7307741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307797 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 10]
def baseStart_7307797 : Nat := 118140960795 + 7307797 * 2 ^ 59
def prefixEnd_7307797 : Nat := 4983230072969 + 3 ^ 40 * 7307797 * 2
def baseEnd_7307797 : Nat := 416934709609405549369951

theorem tailTrace_7307797 : CollatzResearch.WordTrace tailWord_7307797 prefixEnd_7307797 416934709609405549369951 := by
  unfold tailWord_7307797
  simp only [CollatzResearch.WordTrace]
  refine ⟨266537253506107016208593645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177691502337404677472395763 266537253506107016208593645)
  ·
    refine ⟨99951470064790131078222617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266537253506107016208593645 99951470064790131078222617)
    ·
      refine ⟨74963602548592598308666963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99951470064790131078222617 74963602548592598308666963)
      ·
        refine ⟨112445403822888897463000445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74963602548592598308666963 112445403822888897463000445)
        ·
          refine ⟨42167026433583336548625167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112445403822888897463000445 42167026433583336548625167)
          ·
            refine ⟨63250539650375004822937751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42167026433583336548625167 63250539650375004822937751)
            ·
              refine ⟨94875809475562507234406627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63250539650375004822937751 94875809475562507234406627)
              ·
                refine ⟨142313714213343760851609941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94875809475562507234406627 142313714213343760851609941)
                ·
                  refine ⟨416934709609405549369951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142313714213343760851609941 416934709609405549369951)
                  ·
                    rfl

theorem cell23_7307797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_7307797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307797 prefixEnd_7307797 := by exact prefixLift 7307797
  have htrace : WordTrace (prefixWord ++ tailWord_7307797) baseStart_7307797 baseEnd_7307797 := by
    simpa [prefixWord, tailWord_7307797, baseEnd_7307797] using wordTrace_append hprefix tailTrace_7307797
  have hstable : (prefixWord ++ tailWord_7307797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307797).length < 2 ^ (prefixWord ++ tailWord_7307797).sum := by decide
  have hdescent : baseEnd_7307797 < baseStart_7307797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307811 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3]
def baseStart_7307811 : Nat := 118140960795 + 7307811 * 2 ^ 59
def prefixEnd_7307811 : Nat := 4983230072969 + 3 ^ 40 * 7307811 * 2
def baseEnd_7307811 : Nat := 3752419575213812889554495

theorem tailTrace_7307811 : CollatzResearch.WordTrace tailWord_7307811 prefixEnd_7307811 3752419575213812889554495 := by
  unfold tailWord_7307811
  simp only [CollatzResearch.WordTrace]
  refine ⟨266537764128056296599603287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177691842752037531066402191 266537764128056296599603287)
  ·
    refine ⟨399806646192084444899404931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266537764128056296599603287 399806646192084444899404931)
    ·
      refine ⟨599709969288126667349107397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399806646192084444899404931 599709969288126667349107397)
      ·
        refine ⟨112445619241523750127957637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599709969288126667349107397 112445619241523750127957637)
        ·
          refine ⟨21083553607785703148992057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112445619241523750127957637 21083553607785703148992057)
          ·
            refine ⟨15812665205839277361744043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21083553607785703148992057 15812665205839277361744043)
            ·
              refine ⟨23718997808758916042616065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15812665205839277361744043 23718997808758916042616065)
              ·
                refine ⟨17789248356569187031962049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23718997808758916042616065 17789248356569187031962049)
                ·
                  refine ⟨13341936267426890273971537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17789248356569187031962049 13341936267426890273971537)
                  ·
                    refine ⟨10006452200570167705478653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13341936267426890273971537 10006452200570167705478653)
                    ·
                      refine ⟨3752419575213812889554495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006452200570167705478653 3752419575213812889554495)
                      ·
                        rfl

theorem cell23_7307811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_7307811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307811 prefixEnd_7307811 := by exact prefixLift 7307811
  have htrace : WordTrace (prefixWord ++ tailWord_7307811) baseStart_7307811 baseEnd_7307811 := by
    simpa [prefixWord, tailWord_7307811, baseEnd_7307811] using wordTrace_append hprefix tailTrace_7307811
  have hstable : (prefixWord ++ tailWord_7307811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307811).length < 2 ^ (prefixWord ++ tailWord_7307811).sum := by decide
  have hdescent : baseEnd_7307811 < baseStart_7307811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307818 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7307818 : Nat := 118140960795 + 7307818 * 2 ^ 59
def prefixEnd_7307818 : Nat := 4983230072969 + 3 ^ 40 * 7307818 * 2
def baseEnd_7307818 : Nat := 1250807723192798120722321

theorem tailTrace_7307818 : CollatzResearch.WordTrace tailWord_7307818 prefixEnd_7307818 1250807723192798120722321 := by
  unfold tailWord_7307818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634504859757734198777027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177692012959353957863405405 66634504859757734198777027)
  ·
    refine ⟨99951757289636601298165541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66634504859757734198777027 99951757289636601298165541)
    ·
      refine ⟨18740954491806862743406039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99951757289636601298165541 18740954491806862743406039)
      ·
        refine ⟨28111431737710294115109059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18740954491806862743406039 28111431737710294115109059)
        ·
          refine ⟨42167147606565441172663589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111431737710294115109059 42167147606565441172663589)
          ·
            refine ⟨7906340176231020219874423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42167147606565441172663589 7906340176231020219874423)
            ·
              refine ⟨11859510264346530329811635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906340176231020219874423 11859510264346530329811635)
              ·
                refine ⟨17789265396519795494717453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859510264346530329811635 17789265396519795494717453)
                ·
                  refine ⟨6670974523694923310519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17789265396519795494717453 6670974523694923310519045)
                  ·
                    refine ⟨1250807723192798120722321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670974523694923310519045 1250807723192798120722321)
                    ·
                      rfl

theorem cell23_7307818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7307818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307818 prefixEnd_7307818 := by exact prefixLift 7307818
  have htrace : WordTrace (prefixWord ++ tailWord_7307818) baseStart_7307818 baseEnd_7307818 := by
    simpa [prefixWord, tailWord_7307818, baseEnd_7307818] using wordTrace_append hprefix tailTrace_7307818
  have hstable : (prefixWord ++ tailWord_7307818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307818).length < 2 ^ (prefixWord ++ tailWord_7307818).sum := by decide
  have hdescent : baseEnd_7307818 < baseStart_7307818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307851 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 2, 3, 2]
def baseStart_7307851 : Nat := 118140960795 + 7307851 * 2 ^ 59
def prefixEnd_7307851 : Nat := 4983230072969 + 3 ^ 40 * 7307851 * 2
def baseEnd_7307851 : Nat := 3752440114439992733054311

theorem tailTrace_7307851 : CollatzResearch.WordTrace tailWord_7307851 prefixEnd_7307851 3752440114439992733054311 := by
  unfold tailWord_7307851
  simp only [CollatzResearch.WordTrace]
  refine ⟨266539223047911383431059407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177692815365274255620706271 266539223047911383431059407)
  ·
    refine ⟨399808834571867075146589111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266539223047911383431059407 399808834571867075146589111)
    ·
      refine ⟨599713251857800612719883667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399808834571867075146589111 599713251857800612719883667)
      ·
        refine ⟨899569877786700919079825501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599713251857800612719883667 899569877786700919079825501)
        ·
          refine ⟨337338704170012844654934563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899569877786700919079825501 337338704170012844654934563)
          ·
            refine ⟨506008056255019266982401845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337338704170012844654934563 506008056255019266982401845)
            ·
              refine ⟨47438255273908056279600173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506008056255019266982401845 47438255273908056279600173)
              ·
                refine ⟨17789345727715521104850065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47438255273908056279600173 17789345727715521104850065)
                ·
                  refine ⟨13342009295786640828637549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17789345727715521104850065 13342009295786640828637549)
                  ·
                    refine ⟨5003253485919990310739081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13342009295786640828637549 5003253485919990310739081)
                    ·
                      refine ⟨3752440114439992733054311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003253485919990310739081 3752440114439992733054311)
                      ·
                        rfl

theorem cell23_7307851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3, 2].length) (baseStart_7307851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307851 prefixEnd_7307851 := by exact prefixLift 7307851
  have htrace : WordTrace (prefixWord ++ tailWord_7307851) baseStart_7307851 baseEnd_7307851 := by
    simpa [prefixWord, tailWord_7307851, baseEnd_7307851] using wordTrace_append hprefix tailTrace_7307851
  have hstable : (prefixWord ++ tailWord_7307851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307851).length < 2 ^ (prefixWord ++ tailWord_7307851).sum := by decide
  have hdescent : baseEnd_7307851 < baseStart_7307851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307884 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_7307884 : Nat := 118140960795 + 7307884 * 2 ^ 59
def prefixEnd_7307884 : Nat := 4983230072969 + 3 ^ 40 * 7307884 * 2
def baseEnd_7307884 : Nat := 3752457059301591103941659

theorem tailTrace_7307884 : CollatzResearch.WordTrace tailWord_7307884 prefixEnd_7307884 3752457059301591103941659 := by
  unfold tailWord_7307884
  simp only [CollatzResearch.WordTrace]
  refine ⟨133270213328395915033505353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177693617771194553378007137 133270213328395915033505353)
  ·
    refine ⟨99952659996296936275129015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133270213328395915033505353 99952659996296936275129015)
    ·
      refine ⟨149928989994445404412693523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99952659996296936275129015 149928989994445404412693523)
      ·
        refine ⟨224893484991668106619040285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149928989994445404412693523 224893484991668106619040285)
        ·
          refine ⟨84335056871875539982140107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224893484991668106619040285 84335056871875539982140107)
          ·
            refine ⟨126502585307813309973210161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84335056871875539982140107 126502585307813309973210161)
            ·
              refine ⟨94876938980859982479907621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126502585307813309973210161 94876938980859982479907621)
              ·
                refine ⟨17789426058911246714982679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94876938980859982479907621 17789426058911246714982679)
                ·
                  refine ⟨26684139088366870072474019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17789426058911246714982679 26684139088366870072474019)
                  ·
                    refine ⟨40026208632550305108711029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26684139088366870072474019 40026208632550305108711029)
                    ·
                      refine ⟨3752457059301591103941659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40026208632550305108711029 3752457059301591103941659)
                      ·
                        rfl

theorem cell23_7307884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_7307884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307884 prefixEnd_7307884 := by exact prefixLift 7307884
  have htrace : WordTrace (prefixWord ++ tailWord_7307884) baseStart_7307884 baseEnd_7307884 := by
    simpa [prefixWord, tailWord_7307884, baseEnd_7307884] using wordTrace_append hprefix tailTrace_7307884
  have hstable : (prefixWord ++ tailWord_7307884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307884).length < 2 ^ (prefixWord ++ tailWord_7307884).sum := by decide
  have hdescent : baseEnd_7307884 < baseStart_7307884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307918 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7307918 : Nat := 118140960795 + 7307918 * 2 ^ 59
def prefixEnd_7307918 : Nat := 4983230072969 + 3 ^ 40 * 7307918 * 2
def baseEnd_7307918 : Nat := 3752474517643843970916503

theorem tailTrace_7307918 : CollatzResearch.WordTrace tailWord_7307918 prefixEnd_7307918 3752474517643843970916503 := by
  unfold tailWord_7307918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317708342333581734218551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177694444492445769249165605 33317708342333581734218551)
  ·
    refine ⟨49976562513500372601327827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33317708342333581734218551 49976562513500372601327827)
    ·
      refine ⟨74964843770250558901991741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49976562513500372601327827 74964843770250558901991741)
      ·
        refine ⟨28111816413843959588246903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74964843770250558901991741 28111816413843959588246903)
        ·
          refine ⟨42167724620765939382370355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111816413843959588246903 42167724620765939382370355)
          ·
            refine ⟨63251586931148909073555533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42167724620765939382370355 63251586931148909073555533)
            ·
              refine ⟨23719345099180840902583325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63251586931148909073555533 23719345099180840902583325)
              ·
                refine ⟨8894754412192815338468747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23719345099180840902583325 8894754412192815338468747)
                ·
                  refine ⟨13342131618289223007703121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8894754412192815338468747 13342131618289223007703121)
                  ·
                    refine ⟨10006598713716917255777341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13342131618289223007703121 10006598713716917255777341)
                    ·
                      refine ⟨3752474517643843970916503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10006598713716917255777341 3752474517643843970916503)
                      ·
                        rfl

theorem cell23_7307918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7307918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307918 prefixEnd_7307918 := by exact prefixLift 7307918
  have htrace : WordTrace (prefixWord ++ tailWord_7307918) baseStart_7307918 baseEnd_7307918 := by
    simpa [prefixWord, tailWord_7307918, baseEnd_7307918] using wordTrace_append hprefix tailTrace_7307918
  have hstable : (prefixWord ++ tailWord_7307918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307918).length < 2 ^ (prefixWord ++ tailWord_7307918).sum := by decide
  have hdescent : baseEnd_7307918 < baseStart_7307918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307932 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7307932 : Nat := 118140960795 + 7307932 * 2 ^ 59
def prefixEnd_7307932 : Nat := 4983230072969 + 3 ^ 40 * 7307932 * 2
def baseEnd_7307932 : Nat := 3752481706373006916141439

theorem tailTrace_7307932 : CollatzResearch.WordTrace tailWord_7307932 prefixEnd_7307932 3752481706373006916141439 := by
  unfold tailWord_7307932
  simp only [CollatzResearch.WordTrace]
  refine ⟨133271088680308967132379025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177694784907078622843172033 133271088680308967132379025)
  ·
    refine ⟨99953316510231725349284269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133271088680308967132379025 99953316510231725349284269)
    ·
      refine ⟨37482493691336897005981601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99953316510231725349284269 37482493691336897005981601)
      ·
        refine ⟨28111870268502672754486201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37482493691336897005981601 28111870268502672754486201)
        ·
          refine ⟨21083902701377004565864651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28111870268502672754486201 21083902701377004565864651)
          ·
            refine ⟨31625854052065506848796977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21083902701377004565864651 31625854052065506848796977)
            ·
              refine ⟨23719390539049130136597733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31625854052065506848796977 23719390539049130136597733)
              ·
                refine ⟨4447385726071711900612075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23719390539049130136597733 4447385726071711900612075)
                ·
                  refine ⟨6671078589107567850918113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447385726071711900612075 6671078589107567850918113)
                  ·
                    refine ⟨5003308941830675888188585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671078589107567850918113 5003308941830675888188585)
                    ·
                      refine ⟨3752481706373006916141439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003308941830675888188585 3752481706373006916141439)
                      ·
                        rfl

theorem cell23_7307932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7307932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7307932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7307932 prefixEnd_7307932 := by exact prefixLift 7307932
  have htrace : WordTrace (prefixWord ++ tailWord_7307932) baseStart_7307932 baseEnd_7307932 := by
    simpa [prefixWord, tailWord_7307932, baseEnd_7307932] using wordTrace_append hprefix tailTrace_7307932
  have hstable : (prefixWord ++ tailWord_7307932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307932).length < 2 ^ (prefixWord ++ tailWord_7307932).sum := by decide
  have hdescent : baseEnd_7307932 < baseStart_7307932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308041 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_7308041 : Nat := 118140960795 + 7308041 * 2 ^ 59
def prefixEnd_7308041 : Nat := 4983230072969 + 3 ^ 40 * 7308041 * 2
def baseEnd_7308041 : Nat := 1250845891921448996559479

theorem tailTrace_7308041 : CollatzResearch.WordTrace tailWord_7308041 prefixEnd_7308041 1250845891921448996559479 := by
  unfold tailWord_7308041
  simp only [CollatzResearch.WordTrace]
  refine ⟨266546152917223045880475977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177697435278148697253650651 266546152917223045880475977)
  ·
    refine ⟨199909614687917284410356983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266546152917223045880475977 199909614687917284410356983)
    ·
      refine ⟨299864422031875926615535475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199909614687917284410356983 299864422031875926615535475)
      ·
        refine ⟨449796633047813889923303213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299864422031875926615535475 449796633047813889923303213)
        ·
          refine ⟨168673737392930208721238705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449796633047813889923303213 168673737392930208721238705)
          ·
            refine ⟨126505303044697656540929029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168673737392930208721238705 126505303044697656540929029)
            ·
              refine ⟨23719744320880810601424193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126505303044697656540929029 23719744320880810601424193)
              ·
                refine ⟨17789808240660607951068145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23719744320880810601424193 17789808240660607951068145)
                ·
                  refine ⟨13342356180495455963301109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17789808240660607951068145 13342356180495455963301109)
                  ·
                    refine ⟨1250845891921448996559479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13342356180495455963301109 1250845891921448996559479)
                    ·
                      rfl

theorem cell23_7308041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_7308041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308041 prefixEnd_7308041 := by exact prefixLift 7308041
  have htrace : WordTrace (prefixWord ++ tailWord_7308041) baseStart_7308041 baseEnd_7308041 := by
    simpa [prefixWord, tailWord_7308041, baseEnd_7308041] using wordTrace_append hprefix tailTrace_7308041
  have hstable : (prefixWord ++ tailWord_7308041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308041).length < 2 ^ (prefixWord ++ tailWord_7308041).sum := by decide
  have hdescent : baseEnd_7308041 < baseStart_7308041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308101 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 6]
def baseStart_7308101 : Nat := 118140960795 + 7308101 * 2 ^ 59
def prefixEnd_7308101 : Nat := 4983230072969 + 3 ^ 40 * 7308101 * 2
def baseEnd_7308101 : Nat := 416952053844846306103129

theorem tailTrace_7308101 : CollatzResearch.WordTrace tailWord_7308101 prefixEnd_7308101 416952053844846306103129 := by
  unfold tailWord_7308101
  simp only [CollatzResearch.WordTrace]
  refine ⟨266548341297005676127660157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177698894198003784085106771 266548341297005676127660157)
  ·
    refine ⟨99955627986377128547872559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266548341297005676127660157 99955627986377128547872559)
    ·
      refine ⟨149933441979565692821808839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99955627986377128547872559 149933441979565692821808839)
      ·
        refine ⟨224900162969348539232713259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149933441979565692821808839 224900162969348539232713259)
        ·
          refine ⟨337350244454022808849069889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224900162969348539232713259 337350244454022808849069889)
          ·
            refine ⟨253012683340517106636802417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337350244454022808849069889 253012683340517106636802417)
            ·
              refine ⟨189759512505387829977601813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253012683340517106636802417 189759512505387829977601813)
              ·
                refine ⟨8894977148690054530200085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189759512505387829977601813 8894977148690054530200085)
                ·
                  refine ⟨416952053844846306103129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8894977148690054530200085 416952053844846306103129)
                  ·
                    rfl

theorem cell23_7308101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_7308101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308101 prefixEnd_7308101 := by exact prefixLift 7308101
  have htrace : WordTrace (prefixWord ++ tailWord_7308101) baseStart_7308101 baseEnd_7308101 := by
    simpa [prefixWord, tailWord_7308101, baseEnd_7308101] using wordTrace_append hprefix tailTrace_7308101
  have hstable : (prefixWord ++ tailWord_7308101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308101).length < 2 ^ (prefixWord ++ tailWord_7308101).sum := by decide
  have hdescent : baseEnd_7308101 < baseStart_7308101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308105 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 1, 4]
def baseStart_7308105 : Nat := 118140960795 + 7308105 * 2 ^ 59
def prefixEnd_7308105 : Nat := 4983230072969 + 3 ^ 40 * 7308105 * 2
def baseEnd_7308105 : Nat := 1250856846175411579759381

theorem tailTrace_7308105 : CollatzResearch.WordTrace tailWord_7308105 prefixEnd_7308105 1250856846175411579759381 := by
  unfold tailWord_7308105
  simp only [CollatzResearch.WordTrace]
  refine ⟨266548487188991184810805769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177698991459327456540537179 266548487188991184810805769)
  ·
    refine ⟨199911365391743388608104327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266548487188991184810805769 199911365391743388608104327)
    ·
      refine ⟨299867048087615082912156491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199911365391743388608104327 299867048087615082912156491)
      ·
        refine ⟨449800572131422624368234737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299867048087615082912156491 449800572131422624368234737)
        ·
          refine ⟨337350429098566968276176053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449800572131422624368234737 337350429098566968276176053)
          ·
            refine ⟨31626602727990653275891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337350429098566968276176053 31626602727990653275891505)
            ·
              refine ⟨23719952045992989956918629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31626602727990653275891505 23719952045992989956918629)
              ·
                refine ⟨4447491008623685616922243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23719952045992989956918629 4447491008623685616922243)
                ·
                  refine ⟨6671236512935528425383365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447491008623685616922243 6671236512935528425383365)
                  ·
                    refine ⟨1250856846175411579759381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6671236512935528425383365 1250856846175411579759381)
                    ·
                      rfl

theorem cell23_7308105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_7308105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308105 prefixEnd_7308105 := by exact prefixLift 7308105
  have htrace : WordTrace (prefixWord ++ tailWord_7308105) baseStart_7308105 baseEnd_7308105 := by
    simpa [prefixWord, tailWord_7308105, baseEnd_7308105] using wordTrace_append hprefix tailTrace_7308105
  have hstable : (prefixWord ++ tailWord_7308105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308105).length < 2 ^ (prefixWord ++ tailWord_7308105).sum := by decide
  have hdescent : baseEnd_7308105 < baseStart_7308105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308185 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 5, 2, 2]
def baseStart_7308185 : Nat := 118140960795 + 7308185 * 2 ^ 59
def prefixEnd_7308185 : Nat := 4983230072969 + 3 ^ 40 * 7308185 * 2
def baseEnd_7308185 : Nat := 3752611616978594426277775

theorem tailTrace_7308185 : CollatzResearch.WordTrace tailWord_7308185 prefixEnd_7308185 3752611616978594426277775 := by
  unfold tailWord_7308185
  simp only [CollatzResearch.WordTrace]
  refine ⟨266551405028701358473718009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177700936685800905649145339 266551405028701358473718009)
  ·
    refine ⟨199913553771526018855288507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266551405028701358473718009 199913553771526018855288507)
    ·
      refine ⟨299870330657289028282932761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199913553771526018855288507 299870330657289028282932761)
      ·
        refine ⟨224902747992966771212199571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299870330657289028282932761 224902747992966771212199571)
        ·
          refine ⟨337354121989450156818299357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224902747992966771212199571 337354121989450156818299357)
          ·
            refine ⟨126507795746043808806862259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337354121989450156818299357 126507795746043808806862259)
            ·
              refine ⟨189761693619065713210293389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126507795746043808806862259 189761693619065713210293389)
              ·
                refine ⟨71160635107149642453860021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189761693619065713210293389 71160635107149642453860021)
                ·
                  refine ⟨6671309541295278980049377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71160635107149642453860021 6671309541295278980049377)
                  ·
                    refine ⟨5003482155971459235037033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671309541295278980049377 5003482155971459235037033)
                    ·
                      refine ⟨3752611616978594426277775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003482155971459235037033 3752611616978594426277775)
                      ·
                        rfl

theorem cell23_7308185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_7308185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308185 prefixEnd_7308185 := by exact prefixLift 7308185
  have htrace : WordTrace (prefixWord ++ tailWord_7308185) baseStart_7308185 baseEnd_7308185 := by
    simpa [prefixWord, tailWord_7308185, baseEnd_7308185] using wordTrace_append hprefix tailTrace_7308185
  have hstable : (prefixWord ++ tailWord_7308185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308185).length < 2 ^ (prefixWord ++ tailWord_7308185).sum := by decide
  have hdescent : baseEnd_7308185 < baseStart_7308185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308211 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_7308211 : Nat := 118140960795 + 7308211 * 2 ^ 59
def prefixEnd_7308211 : Nat := 4983230072969 + 3 ^ 40 * 7308211 * 2
def baseEnd_7308211 : Nat := 3752624967475611324552655

theorem tailTrace_7308211 : CollatzResearch.WordTrace tailWord_7308211 prefixEnd_7308211 3752624967475611324552655 := by
  unfold tailWord_7308211
  simp only [CollatzResearch.WordTrace]
  refine ⟨266552353326607164914164487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177701568884404776609442991 266552353326607164914164487)
  ·
    refine ⟨399828529989910747371246731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266552353326607164914164487 399828529989910747371246731)
    ·
      refine ⟨599742794984866121056870097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399828529989910747371246731 599742794984866121056870097)
      ·
        refine ⟨449807096238649590792652573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599742794984866121056870097 449807096238649590792652573)
        ·
          refine ⟨168677661089493596547244715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449807096238649590792652573 168677661089493596547244715)
          ·
            refine ⟨253016491634240394820867073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168677661089493596547244715 253016491634240394820867073)
            ·
              refine ⟨189762368725680296115650305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253016491634240394820867073 189762368725680296115650305)
              ·
                refine ⟨142321776544260222086737729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189762368725680296115650305 142321776544260222086737729)
                ·
                  refine ⟨106741332408195166565053297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142321776544260222086737729 106741332408195166565053297)
                  ·
                    refine ⟨80055999306146374923789973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106741332408195166565053297 80055999306146374923789973)
                    ·
                      refine ⟨3752624967475611324552655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80055999306146374923789973 3752624967475611324552655)
                      ·
                        rfl

theorem cell23_7308211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_7308211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308211 prefixEnd_7308211 := by exact prefixLift 7308211
  have htrace : WordTrace (prefixWord ++ tailWord_7308211) baseStart_7308211 baseEnd_7308211 := by
    simpa [prefixWord, tailWord_7308211, baseEnd_7308211] using wordTrace_append hprefix tailTrace_7308211
  have hstable : (prefixWord ++ tailWord_7308211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308211).length < 2 ^ (prefixWord ++ tailWord_7308211).sum := by decide
  have hdescent : baseEnd_7308211 < baseStart_7308211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308218 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_7308218 : Nat := 118140960795 + 7308218 * 2 ^ 59
def prefixEnd_7308218 : Nat := 4983230072969 + 3 ^ 40 * 7308218 * 2
def baseEnd_7308218 : Nat := 3752628561840192797165123

theorem tailTrace_7308218 : CollatzResearch.WordTrace tailWord_7308218 prefixEnd_7308218 3752628561840192797165123 := by
  unfold tailWord_7308218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66638152159395451277417327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177701739091721203406446205 66638152159395451277417327)
  ·
    refine ⟨99957228239093176916125991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66638152159395451277417327 99957228239093176916125991)
    ·
      refine ⟨149935842358639765374188987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99957228239093176916125991 149935842358639765374188987)
      ·
        refine ⟨224903763537959648061283481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149935842358639765374188987 224903763537959648061283481)
        ·
          refine ⟨168677822653469736045962611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224903763537959648061283481 168677822653469736045962611)
          ·
            refine ⟨253016733980204604068943917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168677822653469736045962611 253016733980204604068943917)
            ·
              refine ⟨94881275242576726525853969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253016733980204604068943917 94881275242576726525853969)
              ·
                refine ⟨71160956431932544894390477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94881275242576726525853969 71160956431932544894390477)
                ·
                  refine ⟨26685358661974704335396429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71160956431932544894390477 26685358661974704335396429)
                  ·
                    refine ⟨10007009498240514125773661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26685358661974704335396429 10007009498240514125773661)
                    ·
                      refine ⟨3752628561840192797165123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007009498240514125773661 3752628561840192797165123)
                      ·
                        rfl

theorem cell23_7308218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_7308218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308218 prefixEnd_7308218 := by exact prefixLift 7308218
  have htrace : WordTrace (prefixWord ++ tailWord_7308218) baseStart_7308218 baseEnd_7308218 := by
    simpa [prefixWord, tailWord_7308218, baseEnd_7308218] using wordTrace_append hprefix tailTrace_7308218
  have hstable : (prefixWord ++ tailWord_7308218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308218).length < 2 ^ (prefixWord ++ tailWord_7308218).sum := by decide
  have hdescent : baseEnd_7308218 < baseStart_7308218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308235 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3]
def baseStart_7308235 : Nat := 118140960795 + 7308235 * 2 ^ 59
def prefixEnd_7308235 : Nat := 4983230072969 + 3 ^ 40 * 7308235 * 2
def baseEnd_7308235 : Nat := 3752637291011319230652545

theorem tailTrace_7308235 : CollatzResearch.WordTrace tailWord_7308235 prefixEnd_7308235 3752637291011319230652545 := by
  unfold tailWord_7308235
  simp only [CollatzResearch.WordTrace]
  refine ⟨266553228678520217013038159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177702152452346811342025439 266553228678520217013038159)
  ·
    refine ⟨399829843017780325519557239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266553228678520217013038159 399829843017780325519557239)
    ·
      refine ⟨599744764526670488279335859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399829843017780325519557239 599744764526670488279335859)
      ·
        refine ⟨899617146790005732419003789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599744764526670488279335859 899617146790005732419003789)
        ·
          refine ⟨337356430046252149657126421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899617146790005732419003789 337356430046252149657126421)
          ·
            refine ⟨15813582658418069515177801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337356430046252149657126421 15813582658418069515177801)
            ·
              refine ⟨11860186993813552136383351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813582658418069515177801 11860186993813552136383351)
              ·
                refine ⟨17790280490720328204575027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860186993813552136383351 17790280490720328204575027)
                ·
                  refine ⟨26685420736080492306862541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17790280490720328204575027 26685420736080492306862541)
                  ·
                    refine ⟨10007032776030184615073453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26685420736080492306862541 10007032776030184615073453)
                    ·
                      refine ⟨3752637291011319230652545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007032776030184615073453 3752637291011319230652545)
                      ·
                        rfl

theorem cell23_7308235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].length) (baseStart_7308235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308235 prefixEnd_7308235 := by exact prefixLift 7308235
  have htrace : WordTrace (prefixWord ++ tailWord_7308235) baseStart_7308235 baseEnd_7308235 := by
    simpa [prefixWord, tailWord_7308235, baseEnd_7308235] using wordTrace_append hprefix tailTrace_7308235
  have hstable : (prefixWord ++ tailWord_7308235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308235).length < 2 ^ (prefixWord ++ tailWord_7308235).sum := by decide
  have hdescent : baseEnd_7308235 < baseStart_7308235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308286 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7308286 : Nat := 118140960795 + 7308286 * 2 ^ 59
def prefixEnd_7308286 : Nat := 4983230072969 + 3 ^ 40 * 7308286 * 2
def baseEnd_7308286 : Nat := 3752663478524698531114811

theorem tailTrace_7308286 : CollatzResearch.WordTrace tailWord_7308286 prefixEnd_7308286 3752663478524698531114811 := by
  unfold tailWord_7308286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33319386100166931590393089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177703392534223635148763141 33319386100166931590393089)
  ·
    refine ⟨24989539575125198692794817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33319386100166931590393089 24989539575125198692794817)
    ·
      refine ⟨18742154681343899019596113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24989539575125198692794817 18742154681343899019596113)
      ·
        refine ⟨14056616011007924264697085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18742154681343899019596113 14056616011007924264697085)
        ·
          refine ⟨5271231004127971599261407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14056616011007924264697085 5271231004127971599261407)
          ·
            refine ⟨7906846506191957398892111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271231004127971599261407 7906846506191957398892111)
            ·
              refine ⟨11860269759287936098338167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906846506191957398892111 11860269759287936098338167)
              ·
                refine ⟨17790404638931904147507251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860269759287936098338167 17790404638931904147507251)
                ·
                  refine ⟨26685606958397856221260877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17790404638931904147507251 26685606958397856221260877)
                  ·
                    refine ⟨10007102609399196082972829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26685606958397856221260877 10007102609399196082972829)
                    ·
                      refine ⟨3752663478524698531114811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007102609399196082972829 3752663478524698531114811)
                      ·
                        rfl

theorem cell23_7308286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7308286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308286 prefixEnd_7308286 := by exact prefixLift 7308286
  have htrace : WordTrace (prefixWord ++ tailWord_7308286) baseStart_7308286 baseEnd_7308286 := by
    simpa [prefixWord, tailWord_7308286, baseEnd_7308286] using wordTrace_append hprefix tailTrace_7308286
  have hstable : (prefixWord ++ tailWord_7308286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308286).length < 2 ^ (prefixWord ++ tailWord_7308286).sum := by decide
  have hdescent : baseEnd_7308286 < baseStart_7308286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308332 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 5]
def baseStart_7308332 : Nat := 118140960795 + 7308332 * 2 ^ 59
def prefixEnd_7308332 : Nat := 4983230072969 + 3 ^ 40 * 7308332 * 2
def baseEnd_7308332 : Nat := 416965233181645039015511

theorem tailTrace_7308332 : CollatzResearch.WordTrace tailWord_7308332 prefixEnd_7308332 416965233181645039015511 := by
  unfold tailWord_7308332
  simp only [CollatzResearch.WordTrace]
  refine ⟨133278383279584401289659625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177704511039445868386212833 133278383279584401289659625)
  ·
    refine ⟨99958787459688300967244719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133278383279584401289659625 99958787459688300967244719)
    ·
      refine ⟨149938181189532451450867079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99958787459688300967244719 149938181189532451450867079)
      ·
        refine ⟨224907271784298677176300619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149938181189532451450867079 224907271784298677176300619)
        ·
          refine ⟨337360907676448015764450929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224907271784298677176300619 337360907676448015764450929)
          ·
            refine ⟨253020680757336011823338197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337360907676448015764450929 253020680757336011823338197)
            ·
              refine ⟨5930172205250062777109489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253020680757336011823338197 5930172205250062777109489)
              ·
                refine ⟨4447629153937547082832117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930172205250062777109489 4447629153937547082832117)
                ·
                  refine ⟨416965233181645039015511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4447629153937547082832117 416965233181645039015511)
                  ·
                    rfl

theorem cell23_7308332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_7308332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308332 prefixEnd_7308332 := by exact prefixLift 7308332
  have htrace : WordTrace (prefixWord ++ tailWord_7308332) baseStart_7308332 baseEnd_7308332 := by
    simpa [prefixWord, tailWord_7308332, baseEnd_7308332] using wordTrace_append hprefix tailTrace_7308332
  have hstable : (prefixWord ++ tailWord_7308332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308332).length < 2 ^ (prefixWord ++ tailWord_7308332).sum := by decide
  have hdescent : baseEnd_7308332 < baseStart_7308332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308449 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7308449 : Nat := 118140960795 + 7308449 * 2 ^ 59
def prefixEnd_7308449 : Nat := 4983230072969 + 3 ^ 40 * 7308449 * 2
def baseEnd_7308449 : Nat := 3752747175871381393376561

theorem tailTrace_7308449 : CollatzResearch.WordTrace tailWord_7308449 prefixEnd_7308449 3752747175871381393376561 := by
  unfold tailWord_7308449
  simp only [CollatzResearch.WordTrace]
  refine ⟨266561033899744931561328401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177707355933163287707552267 266561033899744931561328401)
  ·
    refine ⟨199920775424808698670996301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266561033899744931561328401 199920775424808698670996301)
    ·
      refine ⟨74970290784303262001623613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199920775424808698670996301 74970290784303262001623613)
      ·
        refine ⟨28113859044113723250608855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74970290784303262001623613 28113859044113723250608855)
        ·
          refine ⟨42170788566170584875913283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28113859044113723250608855 42170788566170584875913283)
          ·
            refine ⟨63256182849255877313869925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42170788566170584875913283 63256182849255877313869925)
            ·
              refine ⟨11860534284235476996350611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63256182849255877313869925 11860534284235476996350611)
              ·
                refine ⟨17790801426353215494525917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860534284235476996350611 17790801426353215494525917)
                ·
                  refine ⟨6671550534882455810447219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17790801426353215494525917 6671550534882455810447219)
                  ·
                    refine ⟨10007325802323683715670829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671550534882455810447219 10007325802323683715670829)
                    ·
                      refine ⟨3752747175871381393376561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007325802323683715670829 3752747175871381393376561)
                      ·
                        rfl

theorem cell23_7308449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7308449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308449 prefixEnd_7308449 := by exact prefixLift 7308449
  have htrace : WordTrace (prefixWord ++ tailWord_7308449) baseStart_7308449 baseEnd_7308449 := by
    simpa [prefixWord, tailWord_7308449, baseEnd_7308449] using wordTrace_append hprefix tailTrace_7308449
  have hstable : (prefixWord ++ tailWord_7308449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308449).length < 2 ^ (prefixWord ++ tailWord_7308449).sum := by decide
  have hdescent : baseEnd_7308449 < baseStart_7308449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308485 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_7308485 : Nat := 118140960795 + 7308485 * 2 ^ 59
def prefixEnd_7308485 : Nat := 4983230072969 + 3 ^ 40 * 7308485 * 2
def baseEnd_7308485 : Nat := 3752765661174943252526395

theorem tailTrace_7308485 : CollatzResearch.WordTrace tailWord_7308485 prefixEnd_7308485 3752765661174943252526395 := by
  unfold tailWord_7308485
  simp only [CollatzResearch.WordTrace]
  refine ⟨266562346927614509709638909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177708231285076339806425939 266562346927614509709638909)
  ·
    refine ⟨99960880097855441141114591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266562346927614509709638909 99960880097855441141114591)
    ·
      refine ⟨149941320146783161711671887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99960880097855441141114591 149941320146783161711671887)
      ·
        refine ⟨224911980220174742567507831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149941320146783161711671887 224911980220174742567507831)
        ·
          refine ⟨337367970330262113851261747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224911980220174742567507831 337367970330262113851261747)
          ·
            refine ⟨506051955495393170776892621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337367970330262113851261747 506051955495393170776892621)
            ·
              refine ⟨189769483310772439041334733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506051955495393170776892621 189769483310772439041334733)
              ·
                refine ⟨71163556241539664640500525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189769483310772439041334733 71163556241539664640500525)
                ·
                  refine ⟨26686333590577374240187697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71163556241539664640500525 26686333590577374240187697)
                  ·
                    refine ⟨20014750192933030680140773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26686333590577374240187697 20014750192933030680140773)
                    ·
                      refine ⟨3752765661174943252526395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20014750192933030680140773 3752765661174943252526395)
                      ·
                        rfl

theorem cell23_7308485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_7308485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308485 prefixEnd_7308485 := by exact prefixLift 7308485
  have htrace : WordTrace (prefixWord ++ tailWord_7308485) baseStart_7308485 baseEnd_7308485 := by
    simpa [prefixWord, tailWord_7308485, baseEnd_7308485] using wordTrace_append hprefix tailTrace_7308485
  have hstable : (prefixWord ++ tailWord_7308485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308485).length < 2 ^ (prefixWord ++ tailWord_7308485).sum := by decide
  have hdescent : baseEnd_7308485 < baseStart_7308485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308500 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7308500 : Nat := 118140960795 + 7308500 * 2 ^ 59
def prefixEnd_7308500 : Nat := 4983230072969 + 3 ^ 40 * 7308500 * 2
def baseEnd_7308500 : Nat := 3752773363384760693838827

theorem tailTrace_7308500 : CollatzResearch.WordTrace tailWord_7308500 prefixEnd_7308500 3752773363384760693838827 := by
  unfold tailWord_7308500
  simp only [CollatzResearch.WordTrace]
  refine ⟨133281447011280083635717477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177708596015040111514289969 133281447011280083635717477)
  ·
    refine ⟨24990271314615015681697027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133281447011280083635717477 24990271314615015681697027)
    ·
      refine ⟨37485406971922523522545541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24990271314615015681697027 37485406971922523522545541)
      ·
        refine ⟨7028513807235473160477289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37485406971922523522545541 7028513807235473160477289)
        ·
          refine ⟨5271385355426604870357967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7028513807235473160477289 5271385355426604870357967)
          ·
            refine ⟨7907078033139907305536951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271385355426604870357967 7907078033139907305536951)
            ·
              refine ⟨11860617049709860958305427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907078033139907305536951 11860617049709860958305427)
              ·
                refine ⟨17790925574564791437458141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860617049709860958305427 17790925574564791437458141)
                ·
                  refine ⟨6671597090461796789046803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17790925574564791437458141 6671597090461796789046803)
                  ·
                    refine ⟨10007395635692695183570205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671597090461796789046803 10007395635692695183570205)
                    ·
                      refine ⟨3752773363384760693838827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007395635692695183570205 3752773363384760693838827)
                      ·
                        rfl

theorem cell23_7308500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7308500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308500 prefixEnd_7308500 := by exact prefixLift 7308500
  have htrace : WordTrace (prefixWord ++ tailWord_7308500) baseStart_7308500 baseEnd_7308500 := by
    simpa [prefixWord, tailWord_7308500, baseEnd_7308500] using wordTrace_append hprefix tailTrace_7308500
  have hstable : (prefixWord ++ tailWord_7308500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308500).length < 2 ^ (prefixWord ++ tailWord_7308500).sum := by decide
  have hdescent : baseEnd_7308500 < baseStart_7308500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308556 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_7308556 : Nat := 118140960795 + 7308556 * 2 ^ 59
def prefixEnd_7308556 : Nat := 4983230072969 + 3 ^ 40 * 7308556 * 2
def baseEnd_7308556 : Nat := 3752802118301412474738569

theorem tailTrace_7308556 : CollatzResearch.WordTrace tailWord_7308556 prefixEnd_7308556 3752802118301412474738569 := by
  unfold tailWord_7308556
  simp only [CollatzResearch.WordTrace]
  refine ⟨133282468255178644417736761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177709957673571525890315681 133282468255178644417736761)
  ·
    refine ⟨99961851191383983313302571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133282468255178644417736761 99961851191383983313302571)
    ·
      refine ⟨149942776787075974969953857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99961851191383983313302571 149942776787075974969953857)
      ·
        refine ⟨112457082590306981227465393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149942776787075974969953857 112457082590306981227465393)
        ·
          refine ⟨84342811942730235920599045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112457082590306981227465393 84342811942730235920599045)
          ·
            refine ⟨15814277239261919235112321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84342811942730235920599045 15814277239261919235112321)
            ·
              refine ⟨11860707929446439426334241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15814277239261919235112321 11860707929446439426334241)
              ·
                refine ⟨8895530947084829569750681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11860707929446439426334241 8895530947084829569750681)
                ·
                  refine ⟨6671648210313622177313011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895530947084829569750681 6671648210313622177313011)
                  ·
                    refine ⟨10007472315470433265969517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671648210313622177313011 10007472315470433265969517)
                    ·
                      refine ⟨3752802118301412474738569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007472315470433265969517 3752802118301412474738569)
                      ·
                        rfl

theorem cell23_7308556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_7308556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308556 prefixEnd_7308556 := by exact prefixLift 7308556
  have htrace : WordTrace (prefixWord ++ tailWord_7308556) baseStart_7308556 baseEnd_7308556 := by
    simpa [prefixWord, tailWord_7308556, baseEnd_7308556] using wordTrace_append hprefix tailTrace_7308556
  have hstable : (prefixWord ++ tailWord_7308556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308556).length < 2 ^ (prefixWord ++ tailWord_7308556).sum := by decide
  have hdescent : baseEnd_7308556 < baseStart_7308556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308579 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 4, 2]
def baseStart_7308579 : Nat := 118140960795 + 7308579 * 2 ^ 59
def prefixEnd_7308579 : Nat := 4983230072969 + 3 ^ 40 * 7308579 * 2
def baseEnd_7308579 : Nat := 3752813928356465884750963

theorem tailTrace_7308579 : CollatzResearch.WordTrace tailWord_7308579 prefixEnd_7308579 3752813928356465884750963 := by
  unfold tailWord_7308579
  simp only [CollatzResearch.WordTrace]
  refine ⟨266565775389273963763560791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177710516926182642509040527 266565775389273963763560791)
  ·
    refine ⟨399848663083910945645341187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266565775389273963763560791 399848663083910945645341187)
    ·
      refine ⟨599772994625866418468011781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399848663083910945645341187 599772994625866418468011781)
      ·
        refine ⟨112457436492349953462752209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599772994625866418468011781 112457436492349953462752209)
        ·
          refine ⟨84343077369262465097064157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112457436492349953462752209 84343077369262465097064157)
          ·
            refine ⟨31628654013473424411399059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84343077369262465097064157 31628654013473424411399059)
            ·
              refine ⟨47442981020210136617098589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31628654013473424411399059 47442981020210136617098589)
              ·
                refine ⟨17791117882578801231411971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47442981020210136617098589 17791117882578801231411971)
                ·
                  refine ⟨26686676823868201847117957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17791117882578801231411971 26686676823868201847117957)
                  ·
                    refine ⟨5003751904475287846334617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26686676823868201847117957 5003751904475287846334617)
                    ·
                      refine ⟨3752813928356465884750963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003751904475287846334617 3752813928356465884750963)
                      ·
                        rfl

theorem cell23_7308579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_7308579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308579 prefixEnd_7308579 := by exact prefixLift 7308579
  have htrace : WordTrace (prefixWord ++ tailWord_7308579) baseStart_7308579 baseEnd_7308579 := by
    simpa [prefixWord, tailWord_7308579, baseEnd_7308579] using wordTrace_append hprefix tailTrace_7308579
  have hstable : (prefixWord ++ tailWord_7308579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308579).length < 2 ^ (prefixWord ++ tailWord_7308579).sum := by decide
  have hdescent : baseEnd_7308579 < baseStart_7308579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308596 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7308596 : Nat := 118140960795 + 7308596 * 2 ^ 59
def prefixEnd_7308596 : Nat := 4983230072969 + 3 ^ 40 * 7308596 * 2
def baseEnd_7308596 : Nat := 3752822657527592318238385

theorem tailTrace_7308596 : CollatzResearch.WordTrace tailWord_7308596 prefixEnd_7308596 3752822657527592318238385 := by
  unfold tailWord_7308596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133283197715106187833464821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177710930286808250444619761 133283197715106187833464821)
  ·
    refine ⟨12495299785791205109387327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133283197715106187833464821 12495299785791205109387327)
    ·
      refine ⟨18742949678686807664080991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12495299785791205109387327 18742949678686807664080991)
      ·
        refine ⟨28114424518030211496121487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18742949678686807664080991 28114424518030211496121487)
        ·
          refine ⟨42171636777045317244182231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28114424518030211496121487 42171636777045317244182231)
          ·
            refine ⟨63257455165567975866273347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42171636777045317244182231 63257455165567975866273347)
            ·
              refine ⟨94886182748351963799410021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63257455165567975866273347 94886182748351963799410021)
              ·
                refine ⟨17791159265315993212389379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94886182748351963799410021 17791159265315993212389379)
                ·
                  refine ⟨26686738897973989818584069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17791159265315993212389379 26686738897973989818584069)
                  ·
                    refine ⟨5003763543370123090984513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26686738897973989818584069 5003763543370123090984513)
                    ·
                      refine ⟨3752822657527592318238385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003763543370123090984513 3752822657527592318238385)
                      ·
                        rfl

theorem cell23_7308596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7308596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308596 prefixEnd_7308596 := by exact prefixLift 7308596
  have htrace : WordTrace (prefixWord ++ tailWord_7308596) baseStart_7308596 baseEnd_7308596 := by
    simpa [prefixWord, tailWord_7308596, baseEnd_7308596] using wordTrace_append hprefix tailTrace_7308596
  have hstable : (prefixWord ++ tailWord_7308596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308596).length < 2 ^ (prefixWord ++ tailWord_7308596).sum := by decide
  have hdescent : baseEnd_7308596 < baseStart_7308596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308609 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7308609 : Nat := 118140960795 + 7308609 * 2 ^ 59
def prefixEnd_7308609 : Nat := 4983230072969 + 3 ^ 40 * 7308609 * 2
def baseEnd_7308609 : Nat := 3752829332776100767375825

theorem tailTrace_7308609 : CollatzResearch.WordTrace tailWord_7308609 prefixEnd_7308609 3752829332776100767375825 := by
  unfold tailWord_7308609
  simp only [CollatzResearch.WordTrace]
  refine ⟨266566869579165278887152881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177711246386110185924768587 266566869579165278887152881)
  ·
    refine ⟨199925152184373959165364661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266566869579165278887152881 199925152184373959165364661)
    ·
      refine ⟨18742983017285058671752937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199925152184373959165364661 18742983017285058671752937)
      ·
        refine ⟨14057237262963794003814703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18742983017285058671752937 14057237262963794003814703)
        ·
          refine ⟨21085855894445691005722055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14057237262963794003814703 21085855894445691005722055)
          ·
            refine ⟨31628783841668536508583083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21085855894445691005722055 31628783841668536508583083)
            ·
              refine ⟨47443175762502804762874625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31628783841668536508583083 47443175762502804762874625)
              ·
                refine ⟨35582381821877103572155969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47443175762502804762874625 35582381821877103572155969)
                ·
                  refine ⟨26686786366407827679116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35582381821877103572155969 26686786366407827679116977)
                  ·
                    refine ⟨20015089774805870759337733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26686786366407827679116977 20015089774805870759337733)
                    ·
                      refine ⟨3752829332776100767375825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20015089774805870759337733 3752829332776100767375825)
                      ·
                        rfl

theorem cell23_7308609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7308609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308609 prefixEnd_7308609 := by exact prefixLift 7308609
  have htrace : WordTrace (prefixWord ++ tailWord_7308609) baseStart_7308609 baseEnd_7308609 := by
    simpa [prefixWord, tailWord_7308609, baseEnd_7308609] using wordTrace_append hprefix tailTrace_7308609
  have hstable : (prefixWord ++ tailWord_7308609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308609).length < 2 ^ (prefixWord ++ tailWord_7308609).sum := by decide
  have hdescent : baseEnd_7308609 < baseStart_7308609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308629 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7308629 : Nat := 118140960795 + 7308629 * 2 ^ 59
def prefixEnd_7308629 : Nat := 4983230072969 + 3 ^ 40 * 7308629 * 2
def baseEnd_7308629 : Nat := 3752839602389190689125733

theorem tailTrace_7308629 : CollatzResearch.WordTrace tailWord_7308629 prefixEnd_7308629 3752839602389190689125733 := by
  unfold tailWord_7308629
  simp only [CollatzResearch.WordTrace]
  refine ⟨266567599039092822302880941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177711732692728548201920627 266567599039092822302880941)
  ·
    refine ⟨99962849639659808363580353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266567599039092822302880941 99962849639659808363580353)
    ·
      refine ⟨74972137229744856272685265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99962849639659808363580353 74972137229744856272685265)
      ·
        refine ⟨56229102922308642204513949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74972137229744856272685265 56229102922308642204513949)
        ·
          refine ⟨21085913595865740826692731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56229102922308642204513949 21085913595865740826692731)
          ·
            refine ⟨31628870393798611240039097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21085913595865740826692731 31628870393798611240039097)
            ·
              refine ⟨23721652795348958430029323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31628870393798611240039097 23721652795348958430029323)
              ·
                refine ⟨35582479193023437645043985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23721652795348958430029323 35582479193023437645043985)
                ·
                  refine ⟨26686859394767578233782989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35582479193023437645043985 26686859394767578233782989)
                  ·
                    refine ⟨10007572273037841837668621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26686859394767578233782989 10007572273037841837668621)
                    ·
                      refine ⟨3752839602389190689125733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007572273037841837668621 3752839602389190689125733)
                      ·
                        rfl

theorem cell23_7308629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7308629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308629 prefixEnd_7308629 := by exact prefixLift 7308629
  have htrace : WordTrace (prefixWord ++ tailWord_7308629) baseStart_7308629 baseEnd_7308629 := by
    simpa [prefixWord, tailWord_7308629, baseEnd_7308629] using wordTrace_append hprefix tailTrace_7308629
  have hstable : (prefixWord ++ tailWord_7308629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308629).length < 2 ^ (prefixWord ++ tailWord_7308629).sum := by decide
  have hdescent : baseEnd_7308629 < baseStart_7308629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308669 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_7308669 : Nat := 118140960795 + 7308669 * 2 ^ 59
def prefixEnd_7308669 : Nat := 4983230072969 + 3 ^ 40 * 7308669 * 2
def baseEnd_7308669 : Nat := 3752860141615370532625549

theorem tailTrace_7308669 : CollatzResearch.WordTrace tailWord_7308669 prefixEnd_7308669 3752860141615370532625549 := by
  unfold tailWord_7308669
  simp only [CollatzResearch.WordTrace]
  refine ⟨266569057958947909134337061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177712705305965272756224707 266569057958947909134337061)
  ·
    refine ⟨49981698367302732962688199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266569057958947909134337061 49981698367302732962688199)
    ·
      refine ⟨74972547550954099444032299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49981698367302732962688199 74972547550954099444032299)
      ·
        refine ⟨112458821326431149166048449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74972547550954099444032299 112458821326431149166048449)
        ·
          refine ⟨84344115994823361874536337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112458821326431149166048449 84344115994823361874536337)
          ·
            refine ⟨63258086996117521405902253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84344115994823361874536337 63258086996117521405902253)
            ·
              refine ⟨23721782623544070527213345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63258086996117521405902253 23721782623544070527213345)
              ·
                refine ⟨17791336967658052895410009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23721782623544070527213345 17791336967658052895410009)
                ·
                  refine ⟨13343502725743539671557507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17791336967658052895410009 13343502725743539671557507)
                  ·
                    refine ⟨20015254088615309507336261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13343502725743539671557507 20015254088615309507336261)
                    ·
                      refine ⟨3752860141615370532625549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20015254088615309507336261 3752860141615370532625549)
                      ·
                        rfl

theorem cell23_7308669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_7308669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308669 prefixEnd_7308669 := by exact prefixLift 7308669
  have htrace : WordTrace (prefixWord ++ tailWord_7308669) baseStart_7308669 baseEnd_7308669 := by
    simpa [prefixWord, tailWord_7308669, baseEnd_7308669] using wordTrace_append hprefix tailTrace_7308669
  have hstable : (prefixWord ++ tailWord_7308669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308669).length < 2 ^ (prefixWord ++ tailWord_7308669).sum := by decide
  have hdescent : baseEnd_7308669 < baseStart_7308669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308670 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_7308670 : Nat := 118140960795 + 7308670 * 2 ^ 59
def prefixEnd_7308670 : Nat := 4983230072969 + 3 ^ 40 * 7308670 * 2
def baseEnd_7308670 : Nat := 416984517232891669857005

theorem tailTrace_7308670 : CollatzResearch.WordTrace tailWord_7308670 prefixEnd_7308670 416984517232891669857005 := by
  unfold tailWord_7308670
  simp only [CollatzResearch.WordTrace]
  refine ⟨33321136803993035788140433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177712729621296190870082309 33321136803993035788140433)
  ·
    refine ⟨24990852602994776841105325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33321136803993035788140433 24990852602994776841105325)
    ·
      refine ⟨9371569726123041315414497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24990852602994776841105325 9371569726123041315414497)
      ·
        refine ⟨7028677294592280986560873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9371569726123041315414497 7028677294592280986560873)
        ·
          refine ⟨5271507970944210739920655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7028677294592280986560873 5271507970944210739920655)
          ·
            refine ⟨7907261956416316109880983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271507970944210739920655 7907261956416316109880983)
            ·
              refine ⟨11860892934624474164821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907261956416316109880983 11860892934624474164821475)
              ·
                refine ⟨17791339401936711247232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860892934624474164821475 17791339401936711247232213)
                ·
                  refine ⟨416984517232891669857005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17791339401936711247232213 416984517232891669857005)
                  ·
                    rfl

theorem cell23_7308670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_7308670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308670 prefixEnd_7308670 := by exact prefixLift 7308670
  have htrace : WordTrace (prefixWord ++ tailWord_7308670) baseStart_7308670 baseEnd_7308670 := by
    simpa [prefixWord, tailWord_7308670, baseEnd_7308670] using wordTrace_append hprefix tailTrace_7308670
  have hstable : (prefixWord ++ tailWord_7308670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308670).length < 2 ^ (prefixWord ++ tailWord_7308670).sum := by decide
  have hdescent : baseEnd_7308670 < baseStart_7308670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308706 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7308706 : Nat := 118140960795 + 7308706 * 2 ^ 59
def prefixEnd_7308706 : Nat := 4983230072969 + 3 ^ 40 * 7308706 * 2
def baseEnd_7308706 : Nat := 3752879140399586887862879

theorem tailTrace_7308706 : CollatzResearch.WordTrace tailWord_7308706 prefixEnd_7308706 3752879140399586887862879 := by
  unfold tailWord_7308706
  simp only [CollatzResearch.WordTrace]
  refine ⟨66642601864953466113358493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177713604973209242968955981 66642601864953466113358493)
  ·
    refine ⟨24990975699357549792509435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66642601864953466113358493 24990975699357549792509435)
    ·
      refine ⟨37486463549036324688764153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24990975699357549792509435 37486463549036324688764153)
      ·
        refine ⟨28114847661777243516573115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37486463549036324688764153 28114847661777243516573115)
        ·
          refine ⟨42172271492665865274859673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28114847661777243516573115 42172271492665865274859673)
          ·
            refine ⟨31629203619499398956144755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42172271492665865274859673 31629203619499398956144755)
            ·
              refine ⟨47443805429249098434217133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31629203619499398956144755 47443805429249098434217133)
              ·
                refine ⟨17791427035968411912831425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47443805429249098434217133 17791427035968411912831425)
                ·
                  refine ⟨13343570276976308934623569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17791427035968411912831425 13343570276976308934623569)
                  ·
                    refine ⟨10007677707732231700967677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13343570276976308934623569 10007677707732231700967677)
                    ·
                      refine ⟨3752879140399586887862879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007677707732231700967677 3752879140399586887862879)
                      ·
                        rfl

theorem cell23_7308706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7308706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308706 prefixEnd_7308706 := by exact prefixLift 7308706
  have htrace : WordTrace (prefixWord ++ tailWord_7308706) baseStart_7308706 baseEnd_7308706 := by
    simpa [prefixWord, tailWord_7308706, baseEnd_7308706] using wordTrace_append hprefix tailTrace_7308706
  have hstable : (prefixWord ++ tailWord_7308706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308706).length < 2 ^ (prefixWord ++ tailWord_7308706).sum := by decide
  have hdescent : baseEnd_7308706 < baseStart_7308706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308752 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_7308752 : Nat := 118140960795 + 7308752 * 2 ^ 59
def prefixEnd_7308752 : Nat := 4983230072969 + 3 ^ 40 * 7308752 * 2
def baseEnd_7308752 : Nat := 1250967586836564569295889

theorem tailTrace_7308752 : CollatzResearch.WordTrace tailWord_7308752 prefixEnd_7308752 1250967586836564569295889 := by
  unfold tailWord_7308752
  simp only [CollatzResearch.WordTrace]
  refine ⟨133286042608823607154804255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177714723478431476206405673 133286042608823607154804255)
  ·
    refine ⟨199929063913235410732206383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133286042608823607154804255 199929063913235410732206383)
    ·
      refine ⟨299893595869853116098309575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199929063913235410732206383 299893595869853116098309575)
      ·
        refine ⟨449840393804779674147464363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299893595869853116098309575 449840393804779674147464363)
        ·
          refine ⟨674760590707169511221196545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449840393804779674147464363 674760590707169511221196545)
          ·
            refine ⟨506070443030377133415897409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674760590707169511221196545 506070443030377133415897409)
            ·
              refine ⟨379552832272782850061923057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506070443030377133415897409 379552832272782850061923057)
              ·
                refine ⟨284664624204587137546442293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379552832272782850061923057 284664624204587137546442293)
                ·
                  refine ⟨26687308519180044144978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284664624204587137546442293 26687308519180044144978965)
                  ·
                    refine ⟨1250967586836564569295889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26687308519180044144978965 1250967586836564569295889)
                    ·
                      rfl

theorem cell23_7308752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_7308752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308752 prefixEnd_7308752 := by exact prefixLift 7308752
  have htrace : WordTrace (prefixWord ++ tailWord_7308752) baseStart_7308752 baseEnd_7308752 := by
    simpa [prefixWord, tailWord_7308752, baseEnd_7308752] using wordTrace_append hprefix tailTrace_7308752
  have hstable : (prefixWord ++ tailWord_7308752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308752).length < 2 ^ (prefixWord ++ tailWord_7308752).sum := by decide
  have hdescent : baseEnd_7308752 < baseStart_7308752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308769 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7308769 : Nat := 118140960795 + 7308769 * 2 ^ 59
def prefixEnd_7308769 : Nat := 4983230072969 + 3 ^ 40 * 7308769 * 2
def baseEnd_7308769 : Nat := 1250970496560273380458363

theorem tailTrace_7308769 : CollatzResearch.WordTrace tailWord_7308769 prefixEnd_7308769 1250970496560273380458363 := by
  unfold tailWord_7308769
  simp only [CollatzResearch.WordTrace]
  refine ⟨266572705258585626212977361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177715136839057084141984907 266572705258585626212977361)
  ·
    refine ⟨199929528943939219659733021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266572705258585626212977361 199929528943939219659733021)
    ·
      refine ⟨74973573353977207372399883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199929528943939219659733021 74973573353977207372399883)
      ·
        refine ⟨112460360030965811058599825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74973573353977207372399883 112460360030965811058599825)
        ·
          refine ⟨84345270023224358293949869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112460360030965811058599825 84345270023224358293949869)
          ·
            refine ⟨31629476258709134360231201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84345270023224358293949869 31629476258709134360231201)
            ·
              refine ⟨23722107194031850770173401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31629476258709134360231201 23722107194031850770173401)
              ·
                refine ⟨17791580395523888077630051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23722107194031850770173401 17791580395523888077630051)
                ·
                  refine ⟨26687370593285832116445077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17791580395523888077630051 26687370593285832116445077)
                  ·
                    refine ⟨1250970496560273380458363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26687370593285832116445077 1250970496560273380458363)
                    ·
                      rfl

theorem cell23_7308769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7308769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308769 prefixEnd_7308769 := by exact prefixLift 7308769
  have htrace : WordTrace (prefixWord ++ tailWord_7308769) baseStart_7308769 baseEnd_7308769 := by
    simpa [prefixWord, tailWord_7308769, baseEnd_7308769] using wordTrace_append hprefix tailTrace_7308769
  have hstable : (prefixWord ++ tailWord_7308769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308769).length < 2 ^ (prefixWord ++ tailWord_7308769).sum := by decide
  have hdescent : baseEnd_7308769 < baseStart_7308769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308773 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_7308773 : Nat := 118140960795 + 7308773 * 2 ^ 59
def prefixEnd_7308773 : Nat := 4983230072969 + 3 ^ 40 * 7308773 * 2
def baseEnd_7308773 : Nat := 1250971181201146041908357

theorem tailTrace_7308773 : CollatzResearch.WordTrace tailWord_7308773 prefixEnd_7308773 1250971181201146041908357 := by
  unfold tailWord_7308773
  simp only [CollatzResearch.WordTrace]
  refine ⟨266572851150571134896122973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177715234100380756597415315 266572851150571134896122973)
  ·
    refine ⟨99964819181464175586046115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266572851150571134896122973 99964819181464175586046115)
    ·
      refine ⟨149947228772196263379069173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99964819181464175586046115 149947228772196263379069173)
      ·
        refine ⟨14057552697393399691787735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149947228772196263379069173 14057552697393399691787735)
        ·
          refine ⟨21086329046090099537681603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14057552697393399691787735 21086329046090099537681603)
          ·
            refine ⟨31629493569135149306522405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21086329046090099537681603 31629493569135149306522405)
            ·
              refine ⟨5930530044212840494972951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31629493569135149306522405 5930530044212840494972951)
              ·
                refine ⟨8895795066319260742459427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930530044212840494972951 8895795066319260742459427)
                ·
                  refine ⟨13343692599478891113689141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8895795066319260742459427 13343692599478891113689141)
                  ·
                    refine ⟨1250971181201146041908357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13343692599478891113689141 1250971181201146041908357)
                    ·
                      rfl

theorem cell23_7308773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_7308773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308773 prefixEnd_7308773 := by exact prefixLift 7308773
  have htrace : WordTrace (prefixWord ++ tailWord_7308773) baseStart_7308773 baseEnd_7308773 := by
    simpa [prefixWord, tailWord_7308773, baseEnd_7308773] using wordTrace_append hprefix tailTrace_7308773
  have hstable : (prefixWord ++ tailWord_7308773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308773).length < 2 ^ (prefixWord ++ tailWord_7308773).sum := by decide
  have hdescent : baseEnd_7308773 < baseStart_7308773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308776 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7308776 : Nat := 118140960795 + 7308776 * 2 ^ 59
def prefixEnd_7308776 : Nat := 4983230072969 + 3 ^ 40 * 7308776 * 2
def baseEnd_7308776 : Nat := 3752915084045401613987557

theorem tailTrace_7308776 : CollatzResearch.WordTrace tailWord_7308776 prefixEnd_7308776 3752915084045401613987557 := by
  unfold tailWord_7308776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133286480284780133204241091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177715307046373510938988121 133286480284780133204241091)
  ·
    refine ⟨199929720427170199806361637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133286480284780133204241091 199929720427170199806361637)
    ·
      refine ⟨37486822580094412463692807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199929720427170199806361637 37486822580094412463692807)
      ·
        refine ⟨56230233870141618695539211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37486822580094412463692807 56230233870141618695539211)
        ·
          refine ⟨84345350805212428043308817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56230233870141618695539211 84345350805212428043308817)
          ·
            refine ⟨63259013103909321032481613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84345350805212428043308817 63259013103909321032481613)
            ·
              refine ⟨23722129913965995387180605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63259013103909321032481613 23722129913965995387180605)
              ·
                refine ⟨8895798717737248270192727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23722129913965995387180605 8895798717737248270192727)
                ·
                  refine ⟨13343698076605872405289091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8895798717737248270192727 13343698076605872405289091)
                  ·
                    refine ⟨20015547114908808607933637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13343698076605872405289091 20015547114908808607933637)
                    ·
                      refine ⟨3752915084045401613987557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20015547114908808607933637 3752915084045401613987557)
                      ·
                        rfl

theorem cell23_7308776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7308776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308776 prefixEnd_7308776 := by exact prefixLift 7308776
  have htrace : WordTrace (prefixWord ++ tailWord_7308776) baseStart_7308776 baseEnd_7308776 := by
    simpa [prefixWord, tailWord_7308776, baseEnd_7308776] using wordTrace_append hprefix tailTrace_7308776
  have hstable : (prefixWord ++ tailWord_7308776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308776).length < 2 ^ (prefixWord ++ tailWord_7308776).sum := by decide
  have hdescent : baseEnd_7308776 < baseStart_7308776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308779 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3]
def baseStart_7308779 : Nat := 118140960795 + 7308779 * 2 ^ 59
def prefixEnd_7308779 : Nat := 4983230072969 + 3 ^ 40 * 7308779 * 2
def baseEnd_7308779 : Nat := 3752916624487365102250043

theorem tailTrace_7308779 : CollatzResearch.WordTrace tailWord_7308779 prefixEnd_7308779 3752916624487365102250043 := by
  unfold tailWord_7308779
  simp only [CollatzResearch.WordTrace]
  refine ⟨266573069988549397920841391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177715379992366265280560927 266573069988549397920841391)
  ·
    refine ⟨399859604982824096881262087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266573069988549397920841391 399859604982824096881262087)
    ·
      refine ⟨599789407474236145321893131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399859604982824096881262087 599789407474236145321893131)
      ·
        refine ⟨899684111211354217982839697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599789407474236145321893131 899684111211354217982839697)
        ·
          refine ⟨674763083408515663487129773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899684111211354217982839697 674763083408515663487129773)
          ·
            refine ⟨253036156278193373807673665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674763083408515663487129773 253036156278193373807673665)
            ·
              refine ⟨189777117208645030355755249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253036156278193373807673665 189777117208645030355755249)
              ·
                refine ⟨142332837906483772766816437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189777117208645030355755249 142332837906483772766816437)
                ·
                  refine ⟨13343703553732853696889041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142332837906483772766816437 13343703553732853696889041)
                  ·
                    refine ⟨10007777665299640272666781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13343703553732853696889041 10007777665299640272666781)
                    ·
                      refine ⟨3752916624487365102250043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007777665299640272666781 3752916624487365102250043)
                      ·
                        rfl

theorem cell23_7308779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].length) (baseStart_7308779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308779 prefixEnd_7308779 := by exact prefixLift 7308779
  have htrace : WordTrace (prefixWord ++ tailWord_7308779) baseStart_7308779 baseEnd_7308779 := by
    simpa [prefixWord, tailWord_7308779, baseEnd_7308779] using wordTrace_append hprefix tailTrace_7308779
  have hstable : (prefixWord ++ tailWord_7308779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308779).length < 2 ^ (prefixWord ++ tailWord_7308779).sum := by decide
  have hdescent : baseEnd_7308779 < baseStart_7308779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308849 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7308849 : Nat := 118140960795 + 7308849 * 2 ^ 59
def prefixEnd_7308849 : Nat := 4983230072969 + 3 ^ 40 * 7308849 * 2
def baseEnd_7308849 : Nat := 3752952568133179828374721

theorem tailTrace_7308849 : CollatzResearch.WordTrace tailWord_7308849 prefixEnd_7308849 3752952568133179828374721 := by
  unfold tailWord_7308849
  simp only [CollatzResearch.WordTrace]
  refine ⟨266575623098295799875889601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177717082065530533250593067 266575623098295799875889601)
  ·
    refine ⟨199931717323721849906917201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266575623098295799875889601 199931717323721849906917201)
    ·
      refine ⟨149948787992791387430187901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199931717323721849906917201 149948787992791387430187901)
      ·
        refine ⟨56230795497296770286320463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149948787992791387430187901 56230795497296770286320463)
        ·
          refine ⟨84346193245945155429480695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56230795497296770286320463 84346193245945155429480695)
          ·
            refine ⟨126519289868917733144221043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84346193245945155429480695 126519289868917733144221043)
            ·
              refine ⟨189778934803376599716331565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126519289868917733144221043 189778934803376599716331565)
              ·
                refine ⟨71167100551266224893624337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189778934803376599716331565 71167100551266224893624337)
                ·
                  refine ⟨53375325413449668670218253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71167100551266224893624337 53375325413449668670218253)
                  ·
                    refine ⟨20015747030043625751331845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53375325413449668670218253 20015747030043625751331845)
                    ·
                      refine ⟨3752952568133179828374721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20015747030043625751331845 3752952568133179828374721)
                      ·
                        rfl

theorem cell23_7308849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7308849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308849 prefixEnd_7308849 := by exact prefixLift 7308849
  have htrace : WordTrace (prefixWord ++ tailWord_7308849) baseStart_7308849 baseEnd_7308849 := by
    simpa [prefixWord, tailWord_7308849, baseEnd_7308849] using wordTrace_append hprefix tailTrace_7308849
  have hstable : (prefixWord ++ tailWord_7308849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308849).length < 2 ^ (prefixWord ++ tailWord_7308849).sum := by decide
  have hdescent : baseEnd_7308849 < baseStart_7308849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308854 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7308854 : Nat := 118140960795 + 7308854 * 2 ^ 59
def prefixEnd_7308854 : Nat := 4983230072969 + 3 ^ 40 * 7308854 * 2
def baseEnd_7308854 : Nat := 1250985045178817436270733

theorem tailTrace_7308854 : CollatzResearch.WordTrace tailWord_7308854 prefixEnd_7308854 1250985045178817436270733 := by
  unfold tailWord_7308854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660987841454855358113851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177717203642185123819881077 16660987841454855358113851)
  ·
    refine ⟨24991481762182283037170777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16660987841454855358113851 24991481762182283037170777)
    ·
      refine ⟨18743611321636712277878083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24991481762182283037170777 18743611321636712277878083)
      ·
        refine ⟨28115416982455068416817125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743611321636712277878083 28115416982455068416817125)
        ·
          refine ⟨5271640684210325328153211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28115416982455068416817125 5271640684210325328153211)
          ·
            refine ⟨7907461026315487992229817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271640684210325328153211 7907461026315487992229817)
            ·
              refine ⟨5930595769736615994172363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907461026315487992229817 5930595769736615994172363)
              ·
                refine ⟨8895893654604923991258545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930595769736615994172363 8895893654604923991258545)
                ·
                  refine ⟨6671920240953692993443909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895893654604923991258545 6671920240953692993443909)
                  ·
                    refine ⟨1250985045178817436270733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6671920240953692993443909 1250985045178817436270733)
                    ·
                      rfl

theorem cell23_7308854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7308854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308854 prefixEnd_7308854 := by exact prefixLift 7308854
  have htrace : WordTrace (prefixWord ++ tailWord_7308854) baseStart_7308854 baseEnd_7308854 := by
    simpa [prefixWord, tailWord_7308854, baseEnd_7308854] using wordTrace_append hprefix tailTrace_7308854
  have hstable : (prefixWord ++ tailWord_7308854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308854).length < 2 ^ (prefixWord ++ tailWord_7308854).sum := by decide
  have hdescent : baseEnd_7308854 < baseStart_7308854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308860 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_7308860 : Nat := 118140960795 + 7308860 * 2 ^ 59
def prefixEnd_7308860 : Nat := 4983230072969 + 3 ^ 40 * 7308860 * 2
def baseEnd_7308860 : Nat := 3752958216420379285337171

theorem tailTrace_7308860 : CollatzResearch.WordTrace tailWord_7308860 prefixEnd_7308860 3752958216420379285337171 := by
  unfold tailWord_7308860
  simp only [CollatzResearch.WordTrace]
  refine ⟨133288012150627974377270017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177717349534170632503026689 133288012150627974377270017)
  ·
    refine ⟨99966009112970980782952513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133288012150627974377270017 99966009112970980782952513)
    ·
      refine ⟨74974506834728235587214385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99966009112970980782952513 74974506834728235587214385)
      ·
        refine ⟨56230880126046176690410789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74974506834728235587214385 56230880126046176690410789)
        ·
          refine ⟨10543290023633658129452023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56230880126046176690410789 10543290023633658129452023)
          ·
            refine ⟨15814935035450487194178035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543290023633658129452023 15814935035450487194178035)
            ·
              refine ⟨23722402553175730791267053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15814935035450487194178035 23722402553175730791267053)
              ·
                refine ⟨8895900957440899046725145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23722402553175730791267053 8895900957440899046725145)
                ·
                  refine ⟨6671925718080674285043859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895900957440899046725145 6671925718080674285043859)
                  ·
                    refine ⟨10007888577121011427565789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671925718080674285043859 10007888577121011427565789)
                    ·
                      refine ⟨3752958216420379285337171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10007888577121011427565789 3752958216420379285337171)
                      ·
                        rfl

theorem cell23_7308860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_7308860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308860 prefixEnd_7308860 := by exact prefixLift 7308860
  have htrace : WordTrace (prefixWord ++ tailWord_7308860) baseStart_7308860 baseEnd_7308860 := by
    simpa [prefixWord, tailWord_7308860, baseEnd_7308860] using wordTrace_append hprefix tailTrace_7308860
  have hstable : (prefixWord ++ tailWord_7308860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308860).length < 2 ^ (prefixWord ++ tailWord_7308860).sum := by decide
  have hdescent : baseEnd_7308860 < baseStart_7308860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308869 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_7308869 : Nat := 118140960795 + 7308869 * 2 ^ 59
def prefixEnd_7308869 : Nat := 4983230072969 + 3 ^ 40 * 7308869 * 2
def baseEnd_7308869 : Nat := 3752962837746269750124629

theorem tailTrace_7308869 : CollatzResearch.WordTrace tailWord_7308869 prefixEnd_7308869 3752962837746269750124629 := by
  unfold tailWord_7308869
  simp only [CollatzResearch.WordTrace]
  refine ⟨266576352558223343291617661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177717568372148895527745107 266576352558223343291617661)
  ·
    refine ⟨99966132209333753734356623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266576352558223343291617661 99966132209333753734356623)
    ·
      refine ⟨149949198314000630601534935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99966132209333753734356623 149949198314000630601534935)
      ·
        refine ⟨224923797471000945902302403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149949198314000630601534935 224923797471000945902302403)
        ·
          refine ⟨337385696206501418853453605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224923797471000945902302403 337385696206501418853453605)
          ·
            refine ⟨63259818038719016035022551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337385696206501418853453605 63259818038719016035022551)
            ·
              refine ⟨94889727058078524052533827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63259818038719016035022551 94889727058078524052533827)
              ·
                refine ⟨142334590587117786078800741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94889727058078524052533827 142334590587117786078800741)
                ·
                  refine ⟨26687735735084584889775139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142334590587117786078800741 26687735735084584889775139)
                  ·
                    refine ⟨40031603602626877334662709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26687735735084584889775139 40031603602626877334662709)
                    ·
                      refine ⟨3752962837746269750124629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40031603602626877334662709 3752962837746269750124629)
                      ·
                        rfl

theorem cell23_7308869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_7308869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308869 prefixEnd_7308869 := by exact prefixLift 7308869
  have htrace : WordTrace (prefixWord ++ tailWord_7308869) baseStart_7308869 baseEnd_7308869 := by
    simpa [prefixWord, tailWord_7308869, baseEnd_7308869] using wordTrace_append hprefix tailTrace_7308869
  have hstable : (prefixWord ++ tailWord_7308869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308869).length < 2 ^ (prefixWord ++ tailWord_7308869).sum := by decide
  have hdescent : baseEnd_7308869 < baseStart_7308869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308879 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_7308879 : Nat := 118140960795 + 7308879 * 2 ^ 59
def prefixEnd_7308879 : Nat := 4983230072969 + 3 ^ 40 * 7308879 * 2
def baseEnd_7308879 : Nat := 3752967972552814710999583

theorem tailTrace_7308879 : CollatzResearch.WordTrace tailWord_7308879 prefixEnd_7308879 3752967972552814710999583 := by
  unfold tailWord_7308879
  simp only [CollatzResearch.WordTrace]
  refine ⟨266576717288187114999481691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177717811525458076666321127 266576717288187114999481691)
  ·
    refine ⟨399865075932280672499222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266576717288187114999481691 399865075932280672499222537)
    ·
      refine ⟨299898806949210504374416903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399865075932280672499222537 299898806949210504374416903)
      ·
        refine ⟨449848210423815756561625355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299898806949210504374416903 449848210423815756561625355)
        ·
          refine ⟨674772315635723634842438033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449848210423815756561625355 674772315635723634842438033)
          ·
            refine ⟨506079236726792726131828525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674772315635723634842438033 506079236726792726131828525)
            ·
              refine ⟨189779713772547272299435697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506079236726792726131828525 189779713772547272299435697)
              ·
                refine ⟨142334785329410454224576773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189779713772547272299435697 142334785329410454224576773)
                ·
                  refine ⟨26687772249264460167108145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142334785329410454224576773 26687772249264460167108145)
                  ·
                    refine ⟨20015829186948345125331109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26687772249264460167108145 20015829186948345125331109)
                    ·
                      refine ⟨3752967972552814710999583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20015829186948345125331109 3752967972552814710999583)
                      ·
                        rfl

theorem cell23_7308879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_7308879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308879 prefixEnd_7308879 := by exact prefixLift 7308879
  have htrace : WordTrace (prefixWord ++ tailWord_7308879) baseStart_7308879 baseEnd_7308879 := by
    simpa [prefixWord, tailWord_7308879, baseEnd_7308879] using wordTrace_append hprefix tailTrace_7308879
  have hstable : (prefixWord ++ tailWord_7308879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308879).length < 2 ^ (prefixWord ++ tailWord_7308879).sum := by decide
  have hdescent : baseEnd_7308879 < baseStart_7308879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308900 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_7308900 : Nat := 118140960795 + 7308900 * 2 ^ 59
def prefixEnd_7308900 : Nat := 4983230072969 + 3 ^ 40 * 7308900 * 2
def baseEnd_7308900 : Nat := 3752978755646559128836987

theorem tailTrace_7308900 : CollatzResearch.WordTrace tailWord_7308900 prefixEnd_7308900 3752978755646559128836987 := by
  unfold tailWord_7308900
  simp only [CollatzResearch.WordTrace]
  refine ⟨133288741610555517792998077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177718322147407357057330769 133288741610555517792998077)
  ·
    refine ⟨49983278103958319172374279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133288741610555517792998077 49983278103958319172374279)
    ·
      refine ⟨74974917155937478758561419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49983278103958319172374279 74974917155937478758561419)
      ·
        refine ⟨112462375733906218137842129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74974917155937478758561419 112462375733906218137842129)
        ·
          refine ⟨84346781800429663603381597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112462375733906218137842129 84346781800429663603381597)
          ·
            refine ⟨31630043175161123851268099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84346781800429663603381597 31630043175161123851268099)
            ·
              refine ⟨47445064762741685776902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31630043175161123851268099 47445064762741685776902149)
              ·
                refine ⟨8895949643014066083169153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47445064762741685776902149 8895949643014066083169153)
                ·
                  refine ⟨6671962232260549562376865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895949643014066083169153 6671962232260549562376865)
                  ·
                    refine ⟨5003971674195412171782649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671962232260549562376865 5003971674195412171782649)
                    ·
                      refine ⟨3752978755646559128836987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003971674195412171782649 3752978755646559128836987)
                      ·
                        rfl

theorem cell23_7308900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_7308900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308900 prefixEnd_7308900 := by exact prefixLift 7308900
  have htrace : WordTrace (prefixWord ++ tailWord_7308900) baseStart_7308900 baseEnd_7308900 := by
    simpa [prefixWord, tailWord_7308900, baseEnd_7308900] using wordTrace_append hprefix tailTrace_7308900
  have hstable : (prefixWord ++ tailWord_7308900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308900).length < 2 ^ (prefixWord ++ tailWord_7308900).sum := by decide
  have hdescent : baseEnd_7308900 < baseStart_7308900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308917 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7308917 : Nat := 118140960795 + 7308917 * 2 ^ 59
def prefixEnd_7308917 : Nat := 4983230072969 + 3 ^ 40 * 7308917 * 2
def baseEnd_7308917 : Nat := 3752987484817685562324409

theorem tailTrace_7308917 : CollatzResearch.WordTrace tailWord_7308917 prefixEnd_7308917 3752987484817685562324409 := by
  unfold tailWord_7308917
  simp only [CollatzResearch.WordTrace]
  refine ⟨266578103262049447489365005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177718735508032964992910003 266578103262049447489365005)
  ·
    refine ⟨99966788723268542808511877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266578103262049447489365005 99966788723268542808511877)
    ·
      refine ⟨18743772885612851776595977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99966788723268542808511877 18743772885612851776595977)
      ·
        refine ⟨14057829664209638832446983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18743772885612851776595977 14057829664209638832446983)
        ·
          refine ⟨21086744496314458248670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14057829664209638832446983 21086744496314458248670475)
          ·
            refine ⟨31630116744471687373005713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21086744496314458248670475 31630116744471687373005713)
            ·
              refine ⟨23722587558353765529754285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31630116744471687373005713 23722587558353765529754285)
              ·
                refine ⟨8895970334382662073657857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23722587558353765529754285 8895970334382662073657857)
                ·
                  refine ⟨6671977750786996555243393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895970334382662073657857 6671977750786996555243393)
                  ·
                    refine ⟨5003983313090247416432545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671977750786996555243393 5003983313090247416432545)
                    ·
                      refine ⟨3752987484817685562324409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5003983313090247416432545 3752987484817685562324409)
                      ·
                        rfl

theorem cell23_7308917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7308917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308917 prefixEnd_7308917 := by exact prefixLift 7308917
  have htrace : WordTrace (prefixWord ++ tailWord_7308917) baseStart_7308917 baseEnd_7308917 := by
    simpa [prefixWord, tailWord_7308917, baseEnd_7308917] using wordTrace_append hprefix tailTrace_7308917
  have hstable : (prefixWord ++ tailWord_7308917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308917).length < 2 ^ (prefixWord ++ tailWord_7308917).sum := by decide
  have hdescent : baseEnd_7308917 < baseStart_7308917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308919 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 7]
def baseStart_7308919 : Nat := 118140960795 + 7308919 * 2 ^ 59
def prefixEnd_7308919 : Nat := 4983230072969 + 3 ^ 40 * 7308919 * 2
def baseEnd_7308919 : Nat := 1250996170592998184833133

theorem tailTrace_7308919 : CollatzResearch.WordTrace tailWord_7308919 prefixEnd_7308919 1250996170592998184833133 := by
  unfold tailWord_7308919
  simp only [CollatzResearch.WordTrace]
  refine ⟨266578176208042201830937811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177718784138694801220625207 266578176208042201830937811)
  ·
    refine ⟨399867264312063302746406717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266578176208042201830937811 399867264312063302746406717)
    ·
      refine ⟨149950224117023738529902519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399867264312063302746406717 149950224117023738529902519)
      ·
        refine ⟨224925336175535607794853779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149950224117023738529902519 224925336175535607794853779)
        ·
          refine ⟨337388004263303411692280669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224925336175535607794853779 337388004263303411692280669)
          ·
            refine ⟨126520501598738779384605251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337388004263303411692280669 126520501598738779384605251)
            ·
              refine ⟨189780752398108169076907877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126520501598738779384605251 189780752398108169076907877)
              ·
                refine ⟨35583891074645281701920227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189780752398108169076907877 35583891074645281701920227)
                ·
                  refine ⟨53375836611967922552880341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35583891074645281701920227 53375836611967922552880341)
                  ·
                    refine ⟨1250996170592998184833133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53375836611967922552880341 1250996170592998184833133)
                    ·
                      rfl

theorem cell23_7308919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_7308919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308919 prefixEnd_7308919 := by exact prefixLift 7308919
  have htrace : WordTrace (prefixWord ++ tailWord_7308919) baseStart_7308919 baseEnd_7308919 := by
    simpa [prefixWord, tailWord_7308919, baseEnd_7308919] using wordTrace_append hprefix tailTrace_7308919
  have hstable : (prefixWord ++ tailWord_7308919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308919).length < 2 ^ (prefixWord ++ tailWord_7308919).sum := by decide
  have hdescent : baseEnd_7308919 < baseStart_7308919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308949 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7308949 : Nat := 118140960795 + 7308949 * 2 ^ 59
def prefixEnd_7308949 : Nat := 4983230072969 + 3 ^ 40 * 7308949 * 2
def baseEnd_7308949 : Nat := 1251001305399543145708087

theorem tailTrace_7308949 : CollatzResearch.WordTrace tailWord_7308949 prefixEnd_7308949 1251001305399543145708087 := by
  unfold tailWord_7308949
  simp only [CollatzResearch.WordTrace]
  refine ⟨266579270397933516954529901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177719513598622344636353267 266579270397933516954529901)
  ·
    refine ⟨99967226399225068857948713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266579270397933516954529901 99967226399225068857948713)
    ·
      refine ⟨74975419799418801643461535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99967226399225068857948713 74975419799418801643461535)
      ·
        refine ⟨112463129699128202465192303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74975419799418801643461535 112463129699128202465192303)
        ·
          refine ⟨168694694548692303697788455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112463129699128202465192303 168694694548692303697788455)
          ·
            refine ⟨253042041823038455546682683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168694694548692303697788455 253042041823038455546682683)
            ·
              refine ⟨379563062734557683320024025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253042041823038455546682683 379563062734557683320024025)
              ·
                refine ⟨284672297050918262490018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379563062734557683320024025 284672297050918262490018019)
                ·
                  refine ⟨427008445576377393735027029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284672297050918262490018019 427008445576377393735027029)
                  ·
                    refine ⟨1251001305399543145708087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 427008445576377393735027029 1251001305399543145708087)
                    ·
                      rfl

theorem cell23_7308949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7308949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308949 prefixEnd_7308949 := by exact prefixLift 7308949
  have htrace : WordTrace (prefixWord ++ tailWord_7308949) baseStart_7308949 baseEnd_7308949 := by
    simpa [prefixWord, tailWord_7308949, baseEnd_7308949] using wordTrace_append hprefix tailTrace_7308949
  have hstable : (prefixWord ++ tailWord_7308949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308949).length < 2 ^ (prefixWord ++ tailWord_7308949).sum := by decide
  have hdescent : baseEnd_7308949 < baseStart_7308949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308968 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7308968 : Nat := 118140960795 + 7308968 * 2 ^ 59
def prefixEnd_7308968 : Nat := 4983230072969 + 3 ^ 40 * 7308968 * 2
def baseEnd_7308968 : Nat := 3753013672331064862786675

theorem tailTrace_7308968 : CollatzResearch.WordTrace tailWord_7308968 prefixEnd_7308968 3753013672331064862786675 := by
  unfold tailWord_7308968
  simp only [CollatzResearch.WordTrace]
  refine ⟨133289981692432341599735779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177719975589909788799647705 133289981692432341599735779)
  ·
    refine ⟨199934972538648512399603669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133289981692432341599735779 199934972538648512399603669)
    ·
      refine ⟨4685975918874574509365711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 199934972538648512399603669 4685975918874574509365711)
      ·
        refine ⟨7028963878311861764048567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685975918874574509365711 7028963878311861764048567)
        ·
          refine ⟨10543445817467792646072851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028963878311861764048567 10543445817467792646072851)
          ·
            refine ⟨15815168726201688969109277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543445817467792646072851 15815168726201688969109277)
            ·
              refine ⟨5930688272325633363415979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15815168726201688969109277 5930688272325633363415979)
              ·
                refine ⟨8896032408488450045123969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930688272325633363415979 8896032408488450045123969)
                ·
                  refine ⟨6672024306366337533842977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896032408488450045123969 6672024306366337533842977)
                  ·
                    refine ⟨5004018229774753150382233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672024306366337533842977 5004018229774753150382233)
                    ·
                      refine ⟨3753013672331064862786675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004018229774753150382233 3753013672331064862786675)
                      ·
                        rfl

theorem cell23_7308968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7308968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308968 prefixEnd_7308968 := by exact prefixLift 7308968
  have htrace : WordTrace (prefixWord ++ tailWord_7308968) baseStart_7308968 baseEnd_7308968 := by
    simpa [prefixWord, tailWord_7308968, baseEnd_7308968] using wordTrace_append hprefix tailTrace_7308968
  have hstable : (prefixWord ++ tailWord_7308968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308968).length < 2 ^ (prefixWord ++ tailWord_7308968).sum := by decide
  have hdescent : baseEnd_7308968 < baseStart_7308968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_7308969 : Nat := 118140960795 + 7308969 * 2 ^ 59
def prefixEnd_7308969 : Nat := 4983230072969 + 3 ^ 40 * 7308969 * 2
def baseEnd_7308969 : Nat := 3753014185811719358874169

theorem tailTrace_7308969 : CollatzResearch.WordTrace tailWord_7308969 prefixEnd_7308969 3753014185811719358874169 := by
  unfold tailWord_7308969
  simp only [CollatzResearch.WordTrace]
  refine ⟨266579999857861060370257961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177719999905240706913505307 266579999857861060370257961)
  ·
    refine ⟨199934999893395795277693471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266579999857861060370257961 199934999893395795277693471)
    ·
      refine ⟨299902499840093692916540207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199934999893395795277693471 299902499840093692916540207)
      ·
        refine ⟨449853749760140539374810311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299902499840093692916540207 449853749760140539374810311)
        ·
          refine ⟨674780624640210809062215467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449853749760140539374810311 674780624640210809062215467)
          ·
            refine ⟨1012170936960316213593323201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674780624640210809062215467 1012170936960316213593323201)
            ·
              refine ⟨759128202720237160194992401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012170936960316213593323201 759128202720237160194992401)
              ·
                refine ⟨569346152040177870146244301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759128202720237160194992401 569346152040177870146244301)
                ·
                  refine ⟨213504807015066701304841613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569346152040177870146244301 213504807015066701304841613)
                  ·
                    refine ⟨80064302630650012989315605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213504807015066701304841613 80064302630650012989315605)
                    ·
                      refine ⟨3753014185811719358874169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80064302630650012989315605 3753014185811719358874169)
                      ·
                        rfl

theorem cell23_7308969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_7308969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308969 prefixEnd_7308969 := by exact prefixLift 7308969
  have htrace : WordTrace (prefixWord ++ tailWord_7308969) baseStart_7308969 baseEnd_7308969 := by
    simpa [prefixWord, tailWord_7308969, baseEnd_7308969] using wordTrace_append hprefix tailTrace_7308969
  have hstable : (prefixWord ++ tailWord_7308969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308969).length < 2 ^ (prefixWord ++ tailWord_7308969).sum := by decide
  have hdescent : baseEnd_7308969 < baseStart_7308969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308976 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_7308976 : Nat := 118140960795 + 7308976 * 2 ^ 59
def prefixEnd_7308976 : Nat := 4983230072969 + 3 ^ 40 * 7308976 * 2
def baseEnd_7308976 : Nat := 3753017780176300831486637

theorem tailTrace_7308976 : CollatzResearch.WordTrace tailWord_7308976 prefixEnd_7308976 3753017780176300831486637 := by
  unfold tailWord_7308976
  simp only [CollatzResearch.WordTrace]
  refine ⟨133290127584417850282881391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177720170112557133710508521 133290127584417850282881391)
  ·
    refine ⟨199935191376626775424322087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133290127584417850282881391 199935191376626775424322087)
    ·
      refine ⟨299902787064940163136483131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199935191376626775424322087 299902787064940163136483131)
      ·
        refine ⟨449854180597410244704724697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299902787064940163136483131 449854180597410244704724697)
        ·
          refine ⟨337390635448057683528543523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449854180597410244704724697 337390635448057683528543523)
          ·
            refine ⟨506085953172086525292815285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337390635448057683528543523 506085953172086525292815285)
            ·
              refine ⟨47445558109883111746201433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506085953172086525292815285 47445558109883111746201433)
              ·
                refine ⟨35584168582412333809651075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47445558109883111746201433 35584168582412333809651075)
                ·
                  refine ⟨53376252873618500714476613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35584168582412333809651075 53376252873618500714476613)
                  ·
                    refine ⟨10008047413803468883964365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53376252873618500714476613 10008047413803468883964365)
                    ·
                      refine ⟨3753017780176300831486637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008047413803468883964365 3753017780176300831486637)
                      ·
                        rfl

theorem cell23_7308976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_7308976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308976 prefixEnd_7308976 := by exact prefixLift 7308976
  have htrace : WordTrace (prefixWord ++ tailWord_7308976) baseStart_7308976 baseEnd_7308976 := by
    simpa [prefixWord, tailWord_7308976, baseEnd_7308976] using wordTrace_append hprefix tailTrace_7308976
  have hstable : (prefixWord ++ tailWord_7308976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308976).length < 2 ^ (prefixWord ++ tailWord_7308976).sum := by decide
  have hdescent : baseEnd_7308976 < baseStart_7308976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308983 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 3, 4]
def baseStart_7308983 : Nat := 118140960795 + 7308983 * 2 ^ 59
def prefixEnd_7308983 : Nat := 4983230072969 + 3 ^ 40 * 7308983 * 2
def baseEnd_7308983 : Nat := 1251007124846960768033035

theorem tailTrace_7308983 : CollatzResearch.WordTrace tailWord_7308983 prefixEnd_7308983 1251007124846960768033035 := by
  unfold tailWord_7308983
  simp only [CollatzResearch.WordTrace]
  refine ⟨266580510479810340761267603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177720340319873560507511735 266580510479810340761267603)
  ·
    refine ⟨399870765719715511141901405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266580510479810340761267603 399870765719715511141901405)
    ·
      refine ⟨149951537144893316678213027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399870765719715511141901405 149951537144893316678213027)
      ·
        refine ⟨224927305717339975017319541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149951537144893316678213027 224927305717339975017319541)
        ·
          refine ⟨21086934911000622657873707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224927305717339975017319541 21086934911000622657873707)
          ·
            refine ⟨31630402366500933986810561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21086934911000622657873707 31630402366500933986810561)
            ·
              refine ⟨23722801774875700490107921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31630402366500933986810561 23722801774875700490107921)
              ·
                refine ⟨17792101331156775367580941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23722801774875700490107921 17792101331156775367580941)
                ·
                  refine ⟨6672037999183790762842853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17792101331156775367580941 6672037999183790762842853)
                  ·
                    refine ⟨1251007124846960768033035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672037999183790762842853 1251007124846960768033035)
                    ·
                      rfl

theorem cell23_7308983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_7308983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308983 prefixEnd_7308983 := by exact prefixLift 7308983
  have htrace : WordTrace (prefixWord ++ tailWord_7308983) baseStart_7308983 baseEnd_7308983 := by
    simpa [prefixWord, tailWord_7308983, baseEnd_7308983] using wordTrace_append hprefix tailTrace_7308983
  have hstable : (prefixWord ++ tailWord_7308983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308983).length < 2 ^ (prefixWord ++ tailWord_7308983).sum := by decide
  have hdescent : baseEnd_7308983 < baseStart_7308983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7308996 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 10]
def baseStart_7308996 : Nat := 118140960795 + 7308996 * 2 ^ 59
def prefixEnd_7308996 : Nat := 4983230072969 + 3 ^ 40 * 7308996 * 2
def baseEnd_7308996 : Nat := 417003116643265639248505

theorem tailTrace_7308996 : CollatzResearch.WordTrace tailWord_7308996 prefixEnd_7308996 417003116643265639248505 := by
  unfold tailWord_7308996
  simp only [CollatzResearch.WordTrace]
  refine ⟨133290492314381621990745421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177720656419175495987660561 133290492314381621990745421)
  ·
    refine ⟨49983934617893108246529533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133290492314381621990745421 49983934617893108246529533)
    ·
      refine ⟨18743975481709915592448575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49983934617893108246529533 18743975481709915592448575)
      ·
        refine ⟨28115963222564873388672863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743975481709915592448575 28115963222564873388672863)
        ·
          refine ⟨42173944833847310083009295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28115963222564873388672863 42173944833847310083009295)
          ·
            refine ⟨63260917250770965124513943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42173944833847310083009295 63260917250770965124513943)
            ·
              refine ⟨94891375876156447686770915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63260917250770965124513943 94891375876156447686770915)
              ·
                refine ⟨142337063814234671530156373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94891375876156447686770915 142337063814234671530156373)
                ·
                  refine ⟨417003116643265639248505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142337063814234671530156373 417003116643265639248505)
                  ·
                    rfl

theorem cell23_7308996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_7308996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7308996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7308996 prefixEnd_7308996 := by exact prefixLift 7308996
  have htrace : WordTrace (prefixWord ++ tailWord_7308996) baseStart_7308996 baseEnd_7308996 := by
    simpa [prefixWord, tailWord_7308996, baseEnd_7308996] using wordTrace_append hprefix tailTrace_7308996
  have hstable : (prefixWord ++ tailWord_7308996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7308996).length < 2 ^ (prefixWord ++ tailWord_7308996).sum := by decide
  have hdescent : baseEnd_7308996 < baseStart_7308996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7308996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309010 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7309010 : Nat := 118140960795 + 7309010 * 2 ^ 59
def prefixEnd_7309010 : Nat := 4983230072969 + 3 ^ 40 * 7309010 * 2
def baseEnd_7309010 : Nat := 3753035238518553698461481

theorem tailTrace_7309010 : CollatzResearch.WordTrace tailWord_7309010 prefixEnd_7309010 3753035238518553698461481 := by
  unfold tailWord_7309010
  simp only [CollatzResearch.WordTrace]
  refine ⟨66645373812678131093125121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177720996833808349581666989 66645373812678131093125121)
  ·
    refine ⟨49984030359508598319843841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66645373812678131093125121 49984030359508598319843841)
    ·
      refine ⟨37488022769631448739882881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49984030359508598319843841 37488022769631448739882881)
      ·
        refine ⟨28116017077223586554912161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37488022769631448739882881 28116017077223586554912161)
        ·
          refine ⟨21087012807917689916184121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28116017077223586554912161 21087012807917689916184121)
          ·
            refine ⟨15815259605938267437138091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21087012807917689916184121 15815259605938267437138091)
            ·
              refine ⟨23722889408907401155707137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15815259605938267437138091 23722889408907401155707137)
              ·
                refine ⟨17792167056680550866780353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23722889408907401155707137 17792167056680550866780353)
                ·
                  refine ⟨13344125292510413150085265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17792167056680550866780353 13344125292510413150085265)
                  ·
                    refine ⟨10008093969382809862563949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13344125292510413150085265 10008093969382809862563949)
                    ·
                      refine ⟨3753035238518553698461481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008093969382809862563949 3753035238518553698461481)
                      ·
                        rfl

theorem cell23_7309010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7309010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309010 prefixEnd_7309010 := by exact prefixLift 7309010
  have htrace : WordTrace (prefixWord ++ tailWord_7309010) baseStart_7309010 baseEnd_7309010 := by
    simpa [prefixWord, tailWord_7309010, baseEnd_7309010] using wordTrace_append hprefix tailTrace_7309010
  have hstable : (prefixWord ++ tailWord_7309010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309010).length < 2 ^ (prefixWord ++ tailWord_7309010).sum := by decide
  have hdescent : baseEnd_7309010 < baseStart_7309010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309017 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 1, 4]
def baseStart_7309017 : Nat := 118140960795 + 7309017 * 2 ^ 59
def prefixEnd_7309017 : Nat := 4983230072969 + 3 ^ 40 * 7309017 * 2
def baseEnd_7309017 : Nat := 1251012944294378390357983

theorem tailTrace_7309017 : CollatzResearch.WordTrace tailWord_7309017 prefixEnd_7309017 1251012944294378390357983 := by
  unfold tailWord_7309017
  simp only [CollatzResearch.WordTrace]
  refine ⟨266581750561687164568005305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177721167041124776378670203 266581750561687164568005305)
  ·
    refine ⟨199936312921265373426003979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266581750561687164568005305 199936312921265373426003979)
    ·
      refine ⟨299904469381898060139005969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199936312921265373426003979 299904469381898060139005969)
      ·
        refine ⟨224928352036423545104254477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299904469381898060139005969 224928352036423545104254477)
        ·
          refine ⟨84348132013658829414095429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224928352036423545104254477 84348132013658829414095429)
          ·
            refine ⟨15815274752561030515142893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84348132013658829414095429 15815274752561030515142893)
            ·
              refine ⟨5930728032210386443178585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15815274752561030515142893 5930728032210386443178585)
              ·
                refine ⟨4448046024157789832383939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930728032210386443178585 4448046024157789832383939)
                ·
                  refine ⟨6672069036236684748575909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448046024157789832383939 6672069036236684748575909)
                  ·
                    refine ⟨1251012944294378390357983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672069036236684748575909 1251012944294378390357983)
                    ·
                      rfl

theorem cell23_7309017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_7309017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309017 prefixEnd_7309017 := by exact prefixLift 7309017
  have htrace : WordTrace (prefixWord ++ tailWord_7309017) baseStart_7309017 baseEnd_7309017 := by
    simpa [prefixWord, tailWord_7309017, baseEnd_7309017] using wordTrace_append hprefix tailTrace_7309017
  have hstable : (prefixWord ++ tailWord_7309017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309017).length < 2 ^ (prefixWord ++ tailWord_7309017).sum := by decide
  have hdescent : baseEnd_7309017 < baseStart_7309017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309033 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 6, 3, 2]
def baseStart_7309033 : Nat := 118140960795 + 7309033 * 2 ^ 59
def prefixEnd_7309033 : Nat := 4983230072969 + 3 ^ 40 * 7309033 * 2
def baseEnd_7309033 : Nat := 3753047048573607108473875

theorem tailTrace_7309033 : CollatzResearch.WordTrace tailWord_7309033 prefixEnd_7309033 3753047048573607108473875 := by
  unfold tailWord_7309033
  simp only [CollatzResearch.WordTrace]
  refine ⟨266582334129629199300587753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177721556086419466200391835 266582334129629199300587753)
  ·
    refine ⟨199936750597221899475440815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266582334129629199300587753 199936750597221899475440815)
    ·
      refine ⟨299905125895832849213161223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199936750597221899475440815 299905125895832849213161223)
      ·
        refine ⟨449857688843749273819741835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299905125895832849213161223 449857688843749273819741835)
        ·
          refine ⟨674786533265623910729612753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449857688843749273819741835 674786533265623910729612753)
          ·
            refine ⟨506089899949217933047209565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674786533265623910729612753 506089899949217933047209565)
            ·
              refine ⟨189783712480956724892703587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506089899949217933047209565 189783712480956724892703587)
              ·
                refine ⟨284675568721435087339055381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189783712480956724892703587 284675568721435087339055381)
                ·
                  refine ⟨13344167283817269719018221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284675568721435087339055381 13344167283817269719018221)
                  ·
                    refine ⟨5004062731431476144631833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13344167283817269719018221 5004062731431476144631833)
                    ·
                      refine ⟨3753047048573607108473875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004062731431476144631833 3753047048573607108473875)
                      ·
                        rfl

theorem cell23_7309033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3, 2].length) (baseStart_7309033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309033 prefixEnd_7309033 := by exact prefixLift 7309033
  have htrace : WordTrace (prefixWord ++ tailWord_7309033) baseStart_7309033 baseEnd_7309033 := by
    simpa [prefixWord, tailWord_7309033, baseEnd_7309033] using wordTrace_append hprefix tailTrace_7309033
  have hstable : (prefixWord ++ tailWord_7309033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309033).length < 2 ^ (prefixWord ++ tailWord_7309033).sum := by decide
  have hdescent : baseEnd_7309033 < baseStart_7309033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309043 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 1, 5]
def baseStart_7309043 : Nat := 118140960795 + 7309043 * 2 ^ 59
def prefixEnd_7309043 : Nat := 4983230072969 + 3 ^ 40 * 7309043 * 2
def baseEnd_7309043 : Nat := 1251017394460050689782943

theorem tailTrace_7309043 : CollatzResearch.WordTrace tailWord_7309043 prefixEnd_7309043 1251017394460050689782943 := by
  unfold tailWord_7309043
  simp only [CollatzResearch.WordTrace]
  refine ⟨266582698859592971008451783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177721799239728647338967855 266582698859592971008451783)
  ·
    refine ⟨399874048289389456512677675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266582698859592971008451783 399874048289389456512677675)
    ·
      refine ⟨599811072434084184769016513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399874048289389456512677675 599811072434084184769016513)
      ·
        refine ⟨449858304325563138576762385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599811072434084184769016513 449858304325563138576762385)
        ·
          refine ⟨337393728244172353932571789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449858304325563138576762385 337393728244172353932571789)
          ·
            refine ⟨126522648091564632724714421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337393728244172353932571789 126522648091564632724714421)
            ·
              refine ⟨11861498258584184317941977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126522648091564632724714421 11861498258584184317941977)
              ·
                refine ⟨8896123693938138238456483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11861498258584184317941977 8896123693938138238456483)
                ·
                  refine ⟨13344185540907207357684725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896123693938138238456483 13344185540907207357684725)
                  ·
                    refine ⟨1251017394460050689782943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13344185540907207357684725 1251017394460050689782943)
                    ·
                      rfl

theorem cell23_7309043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 5].length) (baseStart_7309043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309043 prefixEnd_7309043 := by exact prefixLift 7309043
  have htrace : WordTrace (prefixWord ++ tailWord_7309043) baseStart_7309043 baseEnd_7309043 := by
    simpa [prefixWord, tailWord_7309043, baseEnd_7309043] using wordTrace_append hprefix tailTrace_7309043
  have hstable : (prefixWord ++ tailWord_7309043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309043).length < 2 ^ (prefixWord ++ tailWord_7309043).sum := by decide
  have hdescent : baseEnd_7309043 < baseStart_7309043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309044 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7309044 : Nat := 118140960795 + 7309044 * 2 ^ 59
def prefixEnd_7309044 : Nat := 4983230072969 + 3 ^ 40 * 7309044 * 2
def baseEnd_7309044 : Nat := 3753052696860806565436325

theorem tailTrace_7309044 : CollatzResearch.WordTrace tailWord_7309044 prefixEnd_7309044 3753052696860806565436325 := by
  unfold tailWord_7309044
  simp only [CollatzResearch.WordTrace]
  refine ⟨133291367666294674089619093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177721823555059565452825457 133291367666294674089619093)
  ·
    refine ⟨6248032859357562847950895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133291367666294674089619093 6248032859357562847950895)
    ·
      refine ⟨9372049289036344271926343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6248032859357562847950895 9372049289036344271926343)
      ·
        refine ⟨14058073933554516407889515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372049289036344271926343 14058073933554516407889515)
        ·
          refine ⟨21087110900331774611834273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058073933554516407889515 21087110900331774611834273)
          ·
            refine ⟨15815333175248830958875705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21087110900331774611834273 15815333175248830958875705)
            ·
              refine ⟨11861499881436623219156779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15815333175248830958875705 11861499881436623219156779)
              ·
                refine ⟨17792249822154934828735169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861499881436623219156779 17792249822154934828735169)
                ·
                  refine ⟨13344187366616201121551377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17792249822154934828735169 13344187366616201121551377)
                  ·
                    refine ⟨10008140524962150841163533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13344187366616201121551377 10008140524962150841163533)
                    ·
                      refine ⟨3753052696860806565436325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008140524962150841163533 3753052696860806565436325)
                      ·
                        rfl

theorem cell23_7309044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7309044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309044 prefixEnd_7309044 := by exact prefixLift 7309044
  have htrace : WordTrace (prefixWord ++ tailWord_7309044) baseStart_7309044 baseEnd_7309044 := by
    simpa [prefixWord, tailWord_7309044, baseEnd_7309044] using wordTrace_append hprefix tailTrace_7309044
  have hstable : (prefixWord ++ tailWord_7309044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309044).length < 2 ^ (prefixWord ++ tailWord_7309044).sum := by decide
  have hdescent : baseEnd_7309044 < baseStart_7309044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309056 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_7309056 : Nat := 118140960795 + 7309056 * 2 ^ 59
def prefixEnd_7309056 : Nat := 4983230072969 + 3 ^ 40 * 7309056 * 2
def baseEnd_7309056 : Nat := 1251019619542886839495423

theorem tailTrace_7309056 : CollatzResearch.WordTrace tailWord_7309056 prefixEnd_7309056 1251019619542886839495423 := by
  unfold tailWord_7309056
  simp only [CollatzResearch.WordTrace]
  refine ⟨133291586504272937114337511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177722115339030582819116681 133291586504272937114337511)
  ·
    refine ⟨199937379756409405671506267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133291586504272937114337511 199937379756409405671506267)
    ·
      refine ⟨299906069634614108507259401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199937379756409405671506267 299906069634614108507259401)
      ·
        refine ⟨224929552225960581380444551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299906069634614108507259401 224929552225960581380444551)
        ·
          refine ⟨337394328338940872070666827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224929552225960581380444551 337394328338940872070666827)
          ·
            refine ⟨506091492508411308106000241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337394328338940872070666827 506091492508411308106000241)
            ·
              refine ⟨379568619381308481079500181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506091492508411308106000241 379568619381308481079500181)
              ·
                refine ⟨17792279033498835050601571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379568619381308481079500181 17792279033498835050601571)
                ·
                  refine ⟨26688418550248252575902357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17792279033498835050601571 26688418550248252575902357)
                  ·
                    refine ⟨1251019619542886839495423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26688418550248252575902357 1251019619542886839495423)
                    ·
                      rfl

theorem cell23_7309056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_7309056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309056 prefixEnd_7309056 := by exact prefixLift 7309056
  have htrace : WordTrace (prefixWord ++ tailWord_7309056) baseStart_7309056 baseEnd_7309056 := by
    simpa [prefixWord, tailWord_7309056, baseEnd_7309056] using wordTrace_append hprefix tailTrace_7309056
  have hstable : (prefixWord ++ tailWord_7309056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309056).length < 2 ^ (prefixWord ++ tailWord_7309056).sum := by decide
  have hdescent : baseEnd_7309056 < baseStart_7309056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309090 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7309090 : Nat := 118140960795 + 7309090 * 2 ^ 59
def prefixEnd_7309090 : Nat := 4983230072969 + 3 ^ 40 * 7309090 * 2
def baseEnd_7309090 : Nat := 1251025438990304461820371

theorem tailTrace_7309090 : CollatzResearch.WordTrace tailWord_7309090 prefixEnd_7309090 1251025438990304461820371 := by
  unfold tailWord_7309090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646103272605674508853181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177722942060281798690275149 66646103272605674508853181)
  ·
    refine ⟨24992288727227127940819943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66646103272605674508853181 24992288727227127940819943)
    ·
      refine ⟨37488433090840691911229915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24992288727227127940819943 37488433090840691911229915)
      ·
        refine ⟨56232649636261037866844873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37488433090840691911229915 56232649636261037866844873)
        ·
          refine ⟨42174487227195778400133655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56232649636261037866844873 42174487227195778400133655)
          ·
            refine ⟨63261730840793667600200483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42174487227195778400133655 63261730840793667600200483)
            ·
              refine ⟨94892596261190501400300725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63261730840793667600200483 94892596261190501400300725)
              ·
                refine ⟨8896180899486609506278193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94892596261190501400300725 8896180899486609506278193)
                ·
                  refine ⟨6672135674614957129708645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896180899486609506278193 6672135674614957129708645)
                  ·
                    refine ⟨1251025438990304461820371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672135674614957129708645 1251025438990304461820371)
                    ·
                      rfl

theorem cell23_7309090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7309090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309090 prefixEnd_7309090 := by exact prefixLift 7309090
  have htrace : WordTrace (prefixWord ++ tailWord_7309090) baseStart_7309090 baseEnd_7309090 := by
    simpa [prefixWord, tailWord_7309090, baseEnd_7309090] using wordTrace_append hprefix tailTrace_7309090
  have hstable : (prefixWord ++ tailWord_7309090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309090).length < 2 ^ (prefixWord ++ tailWord_7309090).sum := by decide
  have hdescent : baseEnd_7309090 < baseStart_7309090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309093 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_7309093 : Nat := 118140960795 + 7309093 * 2 ^ 59
def prefixEnd_7309093 : Nat := 4983230072969 + 3 ^ 40 * 7309093 * 2
def baseEnd_7309093 : Nat := 3753077857412876873723599

theorem tailTrace_7309093 : CollatzResearch.WordTrace tailWord_7309093 prefixEnd_7309093 3753077857412876873723599 := by
  unfold tailWord_7309093
  simp only [CollatzResearch.WordTrace]
  refine ⟨266584522509411829547771933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177723015006274553031847955 266584522509411829547771933)
  ·
    refine ⟨99969195941029436080414475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266584522509411829547771933 99969195941029436080414475)
    ·
      refine ⟨149953793911544154120621713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99969195941029436080414475 149953793911544154120621713)
      ·
        refine ⟨112465345433658115590466285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149953793911544154120621713 112465345433658115590466285)
        ·
          refine ⟨42174504537621793346424857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112465345433658115590466285 42174504537621793346424857)
          ·
            refine ⟨31630878403216345009818643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42174504537621793346424857 31630878403216345009818643)
            ·
              refine ⟨47446317604824517514727965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31630878403216345009818643 47446317604824517514727965)
              ·
                refine ⟨17792369101809194068022987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47446317604824517514727965 17792369101809194068022987)
                ·
                  refine ⟨26688553652713791102034481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17792369101809194068022987 26688553652713791102034481)
                  ·
                    refine ⟨20016415239535343326525861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26688553652713791102034481 20016415239535343326525861)
                    ·
                      refine ⟨3753077857412876873723599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20016415239535343326525861 3753077857412876873723599)
                      ·
                        rfl

theorem cell23_7309093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_7309093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309093 prefixEnd_7309093 := by exact prefixLift 7309093
  have htrace : WordTrace (prefixWord ++ tailWord_7309093) baseStart_7309093 baseEnd_7309093 := by
    simpa [prefixWord, tailWord_7309093, baseEnd_7309093] using wordTrace_append hprefix tailTrace_7309093
  have hstable : (prefixWord ++ tailWord_7309093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309093).length < 2 ^ (prefixWord ++ tailWord_7309093).sum := by decide
  have hdescent : baseEnd_7309093 < baseStart_7309093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309114 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_7309114 : Nat := 118140960795 + 7309114 * 2 ^ 59
def prefixEnd_7309114 : Nat := 4983230072969 + 3 ^ 40 * 7309114 * 2
def baseEnd_7309114 : Nat := 3753088640506621291561003

theorem tailTrace_7309114 : CollatzResearch.WordTrace tailWord_7309114 prefixEnd_7309114 3753088640506621291561003 := by
  unfold tailWord_7309114
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646322110583937533571599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177723525628223833422857597 66646322110583937533571599)
  ·
    refine ⟨99969483165875906300357399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66646322110583937533571599 99969483165875906300357399)
    ·
      refine ⟨149954224748813859450536099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99969483165875906300357399 149954224748813859450536099)
      ·
        refine ⟨224931337123220789175804149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149954224748813859450536099 224931337123220789175804149)
        ·
          refine ⟨21087312855301948985231639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224931337123220789175804149 21087312855301948985231639)
          ·
            refine ⟨31630969282952923477847459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21087312855301948985231639 31630969282952923477847459)
            ·
              refine ⟨47446453924429385216771189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31630969282952923477847459 47446453924429385216771189)
              ·
                refine ⟨4448105055415254864072299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47446453924429385216771189 4448105055415254864072299)
                ·
                  refine ⟨6672157583122882296108449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448105055415254864072299 6672157583122882296108449)
                  ·
                    refine ⟨5004118187342161722081337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672157583122882296108449 5004118187342161722081337)
                    ·
                      refine ⟨3753088640506621291561003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004118187342161722081337 3753088640506621291561003)
                      ·
                        rfl

theorem cell23_7309114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_7309114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309114 prefixEnd_7309114 := by exact prefixLift 7309114
  have htrace : WordTrace (prefixWord ++ tailWord_7309114) baseStart_7309114 baseEnd_7309114 := by
    simpa [prefixWord, tailWord_7309114, baseEnd_7309114] using wordTrace_append hprefix tailTrace_7309114
  have hstable : (prefixWord ++ tailWord_7309114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309114).length < 2 ^ (prefixWord ++ tailWord_7309114).sum := by decide
  have hdescent : baseEnd_7309114 < baseStart_7309114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309117 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7309117 : Nat := 118140960795 + 7309117 * 2 ^ 59
def prefixEnd_7309117 : Nat := 4983230072969 + 3 ^ 40 * 7309117 * 2
def baseEnd_7309117 : Nat := 3753090180948584779823489

theorem tailTrace_7309117 : CollatzResearch.WordTrace tailWord_7309117 prefixEnd_7309117 3753090180948584779823489 := by
  unfold tailWord_7309117
  simp only [CollatzResearch.WordTrace]
  refine ⟨266585397861324881646645605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177723598574216587764430403 266585397861324881646645605)
  ·
    refine ⟨49984762098998415308746051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266585397861324881646645605 49984762098998415308746051)
    ·
      refine ⟨74977143148497622963119077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49984762098998415308746051 74977143148497622963119077)
      ·
        refine ⟨14058214340343304305584827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74977143148497622963119077 14058214340343304305584827)
        ·
          refine ⟨21087321510514956458377241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058214340343304305584827 21087321510514956458377241)
          ·
            refine ⟨15815491132886217343782931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21087321510514956458377241 15815491132886217343782931)
            ·
              refine ⟨23723236699329326015674397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15815491132886217343782931 23723236699329326015674397)
              ·
                refine ⟨8896213762248497255877899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23723236699329326015674397 8896213762248497255877899)
                ·
                  refine ⟨13344320643372745883816849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896213762248497255877899 13344320643372745883816849)
                  ·
                    refine ⟨10008240482529559412862637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13344320643372745883816849 10008240482529559412862637)
                    ·
                      refine ⟨3753090180948584779823489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008240482529559412862637 3753090180948584779823489)
                      ·
                        rfl

theorem cell23_7309117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7309117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309117 prefixEnd_7309117 := by exact prefixLift 7309117
  have htrace : WordTrace (prefixWord ++ tailWord_7309117) baseStart_7309117 baseEnd_7309117 := by
    simpa [prefixWord, tailWord_7309117, baseEnd_7309117] using wordTrace_append hprefix tailTrace_7309117
  have hstable : (prefixWord ++ tailWord_7309117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309117).length < 2 ^ (prefixWord ++ tailWord_7309117).sum := by decide
  have hdescent : baseEnd_7309117 < baseStart_7309117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309130 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_7309130 : Nat := 118140960795 + 7309130 * 2 ^ 59
def prefixEnd_7309130 : Nat := 4983230072969 + 3 ^ 40 * 7309130 * 2
def baseEnd_7309130 : Nat := 3753096856197093228960929

theorem tailTrace_7309130 : CollatzResearch.WordTrace tailWord_7309130 prefixEnd_7309130 3753096856197093228960929 := by
  unfold tailWord_7309130
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646468002569446216717211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177723914673518523244579229 66646468002569446216717211)
  ·
    refine ⟨99969702003854169325075817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66646468002569446216717211 99969702003854169325075817)
    ·
      refine ⟨74977276502890626993806863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99969702003854169325075817 74977276502890626993806863)
      ·
        refine ⟨112465914754335940490710295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74977276502890626993806863 112465914754335940490710295)
        ·
          refine ⟨168698872131503910736065443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112465914754335940490710295 168698872131503910736065443)
          ·
            refine ⟨253048308197255866104098165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168698872131503910736065443 253048308197255866104098165)
            ·
              refine ⟨23723278893492737447259203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253048308197255866104098165 23723278893492737447259203)
              ·
                refine ⟨35584918340239106170888805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23723278893492737447259203 35584918340239106170888805)
                ·
                  refine ⟨6672172188794832407041651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35584918340239106170888805 6672172188794832407041651)
                  ·
                    refine ⟨10008258283192248610562477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6672172188794832407041651 10008258283192248610562477)
                    ·
                      refine ⟨3753096856197093228960929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008258283192248610562477 3753096856197093228960929)
                      ·
                        rfl

theorem cell23_7309130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_7309130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309130 prefixEnd_7309130 := by exact prefixLift 7309130
  have htrace : WordTrace (prefixWord ++ tailWord_7309130) baseStart_7309130 baseEnd_7309130 := by
    simpa [prefixWord, tailWord_7309130, baseEnd_7309130] using wordTrace_append hprefix tailTrace_7309130
  have hstable : (prefixWord ++ tailWord_7309130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309130).length < 2 ^ (prefixWord ++ tailWord_7309130).sum := by decide
  have hdescent : baseEnd_7309130 < baseStart_7309130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309170 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7309170 : Nat := 118140960795 + 7309170 * 2 ^ 59
def prefixEnd_7309170 : Nat := 4983230072969 + 3 ^ 40 * 7309170 * 2
def baseEnd_7309170 : Nat := 3753117395423273072460745

theorem tailTrace_7309170 : CollatzResearch.WordTrace tailWord_7309170 prefixEnd_7309170 3753117395423273072460745 := by
  unfold tailWord_7309170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646832732533217924581241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177724887286755247798883309 66646832732533217924581241)
  ·
    refine ⟨49985124549399913443435931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66646832732533217924581241 49985124549399913443435931)
    ·
      refine ⟨74977686824099870165153897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49985124549399913443435931 74977686824099870165153897)
      ·
        refine ⟨56233265118074902623865423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74977686824099870165153897 56233265118074902623865423)
        ·
          refine ⟨84349897677112353935798135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56233265118074902623865423 84349897677112353935798135)
          ·
            refine ⟨126524846515668530903697203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84349897677112353935798135 126524846515668530903697203)
            ·
              refine ⟨189787269773502796355545805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126524846515668530903697203 189787269773502796355545805)
              ·
                refine ⟨71170226165063548633329677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189787269773502796355545805 71170226165063548633329677)
                ·
                  refine ⟨26688834811898830737498629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71170226165063548633329677 26688834811898830737498629)
                  ·
                    refine ⟨5004156527231030763280993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26688834811898830737498629 5004156527231030763280993)
                    ·
                      refine ⟨3753117395423273072460745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004156527231030763280993 3753117395423273072460745)
                      ·
                        rfl

theorem cell23_7309170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7309170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309170 prefixEnd_7309170 := by exact prefixLift 7309170
  have htrace : WordTrace (prefixWord ++ tailWord_7309170) baseStart_7309170 baseEnd_7309170 := by
    simpa [prefixWord, tailWord_7309170, baseEnd_7309170] using wordTrace_append hprefix tailTrace_7309170
  have hstable : (prefixWord ++ tailWord_7309170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309170).length < 2 ^ (prefixWord ++ tailWord_7309170).sum := by decide
  have hdescent : baseEnd_7309170 < baseStart_7309170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309187 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 4, 2, 2]
def baseStart_7309187 : Nat := 118140960795 + 7309187 * 2 ^ 59
def prefixEnd_7309187 : Nat := 4983230072969 + 3 ^ 40 * 7309187 * 2
def baseEnd_7309187 : Nat := 3753126124594399505948167

theorem tailTrace_7309187 : CollatzResearch.WordTrace tailWord_7309187 prefixEnd_7309187 3753126124594399505948167 := by
  unfold tailWord_7309187
  simp only [CollatzResearch.WordTrace]
  refine ⟨266587950971071283601693815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177725300647380855734462543 266587950971071283601693815)
  ·
    refine ⟨399881926456606925402540723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266587950971071283601693815 399881926456606925402540723)
    ·
      refine ⟨599822889684910388103811085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399881926456606925402540723 599822889684910388103811085)
      ·
        refine ⟨224933583631841395538929157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 599822889684910388103811085 224933583631841395538929157)
        ·
          refine ⟨42175046930970261663549217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224933583631841395538929157 42175046930970261663549217)
          ·
            refine ⟨31631285198227696247661913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42175046930970261663549217 31631285198227696247661913)
            ·
              refine ⟨23723463898670772185746435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31631285198227696247661913 23723463898670772185746435)
              ·
                refine ⟨35585195848006158278619653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23723463898670772185746435 35585195848006158278619653)
                ·
                  refine ⟨6672224221501154677241185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35585195848006158278619653 6672224221501154677241185)
                  ·
                    refine ⟨5004168166125866007930889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672224221501154677241185 5004168166125866007930889)
                    ·
                      refine ⟨3753126124594399505948167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004168166125866007930889 3753126124594399505948167)
                      ·
                        rfl

theorem cell23_7309187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_7309187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309187 prefixEnd_7309187 := by exact prefixLift 7309187
  have htrace : WordTrace (prefixWord ++ tailWord_7309187) baseStart_7309187 baseEnd_7309187 := by
    simpa [prefixWord, tailWord_7309187, baseEnd_7309187] using wordTrace_append hprefix tailTrace_7309187
  have hstable : (prefixWord ++ tailWord_7309187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309187).length < 2 ^ (prefixWord ++ tailWord_7309187).sum := by decide
  have hdescent : baseEnd_7309187 < baseStart_7309187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309198 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7309198 : Nat := 118140960795 + 7309198 * 2 ^ 59
def prefixEnd_7309198 : Nat := 4983230072969 + 3 ^ 40 * 7309198 * 2
def baseEnd_7309198 : Nat := 3753131772881598962910617

theorem tailTrace_7309198 : CollatzResearch.WordTrace tailWord_7309198 prefixEnd_7309198 3753131772881598962910617 := by
  unfold tailWord_7309198
  simp only [CollatzResearch.WordTrace]
  refine ⟨33323544021753929060043031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177725568116020954986896165 33323544021753929060043031)
  ·
    refine ⟨49985316032630893590064547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33323544021753929060043031 49985316032630893590064547)
    ·
      refine ⟨74977974048946340385096821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49985316032630893590064547 74977974048946340385096821)
      ·
        refine ⟨7029185067088719411102827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74977974048946340385096821 7029185067088719411102827)
        ·
          refine ⟨10543777600633079116654241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029185067088719411102827 10543777600633079116654241)
          ·
            refine ⟨7907833200474809337490681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10543777600633079116654241 7907833200474809337490681)
            ·
              refine ⟨5930874900356107003118011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907833200474809337490681 5930874900356107003118011)
              ·
                refine ⟨8896312350534160504677017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930874900356107003118011 8896312350534160504677017)
                ·
                  refine ⟨6672234262900620378507763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896312350534160504677017 6672234262900620378507763)
                  ·
                    refine ⟨10008351394350930567761645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6672234262900620378507763 10008351394350930567761645)
                    ·
                      refine ⟨3753131772881598962910617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008351394350930567761645 3753131772881598962910617)
                      ·
                        rfl

theorem cell23_7309198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7309198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309198 prefixEnd_7309198 := by exact prefixLift 7309198
  have htrace : WordTrace (prefixWord ++ tailWord_7309198) baseStart_7309198 baseEnd_7309198 := by
    simpa [prefixWord, tailWord_7309198, baseEnd_7309198] using wordTrace_append hprefix tailTrace_7309198
  have hstable : (prefixWord ++ tailWord_7309198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309198).length < 2 ^ (prefixWord ++ tailWord_7309198).sum := by decide
  have hdescent : baseEnd_7309198 < baseStart_7309198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309203 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3]
def baseStart_7309203 : Nat := 118140960795 + 7309203 * 2 ^ 59
def prefixEnd_7309203 : Nat := 4983230072969 + 3 ^ 40 * 7309203 * 2
def baseEnd_7309203 : Nat := 3753134340284871443348093

theorem tailTrace_7309203 : CollatzResearch.WordTrace tailWord_7309203 prefixEnd_7309203 3753134340284871443348093 := by
  unfold tailWord_7309203
  simp only [CollatzResearch.WordTrace]
  refine ⟨266588534539013318334276263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177725689692675545556184175 266588534539013318334276263)
  ·
    refine ⟨399882801808519977501414395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266588534539013318334276263 399882801808519977501414395)
    ·
      refine ⟨599824202712779966252121593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399882801808519977501414395 599824202712779966252121593)
      ·
        refine ⟨449868152034584974689091195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599824202712779966252121593 449868152034584974689091195)
        ·
          refine ⟨674802228051877462033636793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449868152034584974689091195 674802228051877462033636793)
          ·
            refine ⟨506101671038908096525227595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674802228051877462033636793 506101671038908096525227595)
            ·
              refine ⟨759152506558362144787841393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506101671038908096525227595 759152506558362144787841393)
              ·
                refine ⟨569364379918771608590881045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759152506558362144787841393 569364379918771608590881045)
                ·
                  refine ⟨26688955308692419152697549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569364379918771608590881045 26688955308692419152697549)
                  ·
                    refine ⟨10008358240759657182261581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26688955308692419152697549 10008358240759657182261581)
                    ·
                      refine ⟨3753134340284871443348093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008358240759657182261581 3753134340284871443348093)
                      ·
                        rfl

theorem cell23_7309203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_7309203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309203 prefixEnd_7309203 := by exact prefixLift 7309203
  have htrace : WordTrace (prefixWord ++ tailWord_7309203) baseStart_7309203 baseEnd_7309203 := by
    simpa [prefixWord, tailWord_7309203, baseEnd_7309203] using wordTrace_append hprefix tailTrace_7309203
  have hstable : (prefixWord ++ tailWord_7309203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309203).length < 2 ^ (prefixWord ++ tailWord_7309203).sum := by decide
  have hdescent : baseEnd_7309203 < baseStart_7309203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309208 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7309208 : Nat := 118140960795 + 7309208 * 2 ^ 59
def prefixEnd_7309208 : Nat := 4983230072969 + 3 ^ 40 * 7309208 * 2
def baseEnd_7309208 : Nat := 3753136907688143923785571

theorem tailTrace_7309208 : CollatzResearch.WordTrace tailWord_7309208 prefixEnd_7309208 3753136907688143923785571 := by
  unfold tailWord_7309208
  simp only [CollatzResearch.WordTrace]
  refine ⟨133294358451997602094104139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177725811269330136125472185 133294358451997602094104139)
  ·
    refine ⟨199941537677996403141156209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133294358451997602094104139 199941537677996403141156209)
    ·
      refine ⟨149956153258497302355867157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199941537677996403141156209 149956153258497302355867157)
      ·
        refine ⟨7029194683992061047931273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149956153258497302355867157 7029194683992061047931273)
        ·
          refine ⟨5271896012994045785948455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7029194683992061047931273 5271896012994045785948455)
          ·
            refine ⟨7907844019491068678922683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271896012994045785948455 7907844019491068678922683)
            ·
              refine ⟨11861766029236603018384025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907844019491068678922683 11861766029236603018384025)
              ·
                refine ⟨8896324521927452263788019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11861766029236603018384025 8896324521927452263788019)
                ·
                  refine ⟨13344486782891178395682029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896324521927452263788019 13344486782891178395682029)
                  ·
                    refine ⟨5004182543584191898380761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13344486782891178395682029 5004182543584191898380761)
                    ·
                      refine ⟨3753136907688143923785571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004182543584191898380761 3753136907688143923785571)
                      ·
                        rfl

theorem cell23_7309208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7309208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309208 prefixEnd_7309208 := by exact prefixLift 7309208
  have htrace : WordTrace (prefixWord ++ tailWord_7309208) baseStart_7309208 baseEnd_7309208 := by
    simpa [prefixWord, tailWord_7309208, baseEnd_7309208] using wordTrace_append hprefix tailTrace_7309208
  have hstable : (prefixWord ++ tailWord_7309208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309208).length < 2 ^ (prefixWord ++ tailWord_7309208).sum := by decide
  have hdescent : baseEnd_7309208 < baseStart_7309208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309244 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 5]
def baseStart_7309244 : Nat := 118140960795 + 7309244 * 2 ^ 59
def prefixEnd_7309244 : Nat := 4983230072969 + 3 ^ 40 * 7309244 * 2
def baseEnd_7309244 : Nat := 417017265887967309215045

theorem tailTrace_7309244 : CollatzResearch.WordTrace tailWord_7309244 prefixEnd_7309244 417017265887967309215045 := by
  unfold tailWord_7309244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133295014965932391168259393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177726686621243188224345857 133295014965932391168259393)
  ·
    refine ⟨99971261224449293376194545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133295014965932391168259393 99971261224449293376194545)
    ·
      refine ⟨74978445918336970032145909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99971261224449293376194545 74978445918336970032145909)
      ·
        refine ⟨7029229304844090940513679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74978445918336970032145909 7029229304844090940513679)
        ·
          refine ⟨10543843957266136410770519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029229304844090940513679 10543843957266136410770519)
          ·
            refine ⟨15815765935899204616155779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543843957266136410770519 15815765935899204616155779)
            ·
              refine ⟨23723648903848806924233669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15815765935899204616155779 23723648903848806924233669)
              ·
                refine ⟨4448184169471651298293813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23723648903848806924233669 4448184169471651298293813)
                ·
                  refine ⟨417017265887967309215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4448184169471651298293813 417017265887967309215045)
                  ·
                    rfl

theorem cell23_7309244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_7309244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309244 prefixEnd_7309244 := by exact prefixLift 7309244
  have htrace : WordTrace (prefixWord ++ tailWord_7309244) baseStart_7309244 baseEnd_7309244 := by
    simpa [prefixWord, tailWord_7309244, baseEnd_7309244] using wordTrace_append hprefix tailTrace_7309244
  have hstable : (prefixWord ++ tailWord_7309244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309244).length < 2 ^ (prefixWord ++ tailWord_7309244).sum := by decide
  have hdescent : baseEnd_7309244 < baseStart_7309244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309274 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_7309274 : Nat := 118140960795 + 7309274 * 2 ^ 59
def prefixEnd_7309274 : Nat := 4983230072969 + 3 ^ 40 * 7309274 * 2
def baseEnd_7309274 : Nat := 1251056932470446888520089

theorem tailTrace_7309274 : CollatzResearch.WordTrace tailWord_7309274 prefixEnd_7309274 1251056932470446888520089 := by
  unfold tailWord_7309274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66647781030439024365027719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177727416081170731640073917 66647781030439024365027719)
  ·
    refine ⟨99971671545658536547541579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66647781030439024365027719 99971671545658536547541579)
    ·
      refine ⟨149957507318487804821312369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99971671545658536547541579 149957507318487804821312369)
      ·
        refine ⟨112468130488865853615984277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149957507318487804821312369 112468130488865853615984277)
        ·
          refine ⟨5271943616665586888249263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112468130488865853615984277 5271943616665586888249263)
          ·
            refine ⟨7907915424998380332373895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271943616665586888249263 7907915424998380332373895)
            ·
              refine ⟨11861873137497570498560843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907915424998380332373895 11861873137497570498560843)
              ·
                refine ⟨17792809706246355747841265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861873137497570498560843 17792809706246355747841265)
                ·
                  refine ⟨13344607279684766810880949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17792809706246355747841265 13344607279684766810880949)
                  ·
                    refine ⟨1251056932470446888520089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13344607279684766810880949 1251056932470446888520089)
                    ·
                      rfl

theorem cell23_7309274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_7309274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309274 prefixEnd_7309274 := by exact prefixLift 7309274
  have htrace : WordTrace (prefixWord ++ tailWord_7309274) baseStart_7309274 baseEnd_7309274 := by
    simpa [prefixWord, tailWord_7309274, baseEnd_7309274] using wordTrace_append hprefix tailTrace_7309274
  have hstable : (prefixWord ++ tailWord_7309274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309274).length < 2 ^ (prefixWord ++ tailWord_7309274).sum := by decide
  have hdescent : baseEnd_7309274 < baseStart_7309274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309277 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_7309277 : Nat := 118140960795 + 7309277 * 2 ^ 59
def prefixEnd_7309277 : Nat := 4983230072969 + 3 ^ 40 * 7309277 * 2
def baseEnd_7309277 : Nat := 3753172337853304153822753

theorem tailTrace_7309277 : CollatzResearch.WordTrace tailWord_7309277 prefixEnd_7309277 3753172337853304153822753 := by
  unfold tailWord_7309277
  simp only [CollatzResearch.WordTrace]
  refine ⟨266591233540745228972470085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177727489027163485981646723 266591233540745228972470085)
  ·
    refine ⟨49985856288889730432338141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266591233540745228972470085 49985856288889730432338141)
    ·
      refine ⟨18744696108333648912126803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49985856288889730432338141 18744696108333648912126803)
      ·
        refine ⟨28117044162500473368190205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744696108333648912126803 28117044162500473368190205)
        ·
          refine ⟨10543891560937677513071327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28117044162500473368190205 10543891560937677513071327)
          ·
            refine ⟨15815837341406516269606991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543891560937677513071327 15815837341406516269606991)
            ·
              refine ⟨23723756012109774404410487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15815837341406516269606991 23723756012109774404410487)
              ·
                refine ⟨35585634018164661606615731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23723756012109774404410487 35585634018164661606615731)
                ·
                  refine ⟨53378451027246992409923597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35585634018164661606615731 53378451027246992409923597)
                  ·
                    refine ⟨20016919135217622153721349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53378451027246992409923597 20016919135217622153721349)
                    ·
                      refine ⟨3753172337853304153822753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20016919135217622153721349 3753172337853304153822753)
                      ·
                        rfl

theorem cell23_7309277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_7309277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309277 prefixEnd_7309277 := by exact prefixLift 7309277
  have htrace : WordTrace (prefixWord ++ tailWord_7309277) baseStart_7309277 baseEnd_7309277 := by
    simpa [prefixWord, tailWord_7309277, baseEnd_7309277] using wordTrace_append hprefix tailTrace_7309277
  have hstable : (prefixWord ++ tailWord_7309277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309277).length < 2 ^ (prefixWord ++ tailWord_7309277).sum := by decide
  have hdescent : baseEnd_7309277 < baseStart_7309277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309317 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 6]
def baseStart_7309317 : Nat := 118140960795 + 7309317 * 2 ^ 59
def prefixEnd_7309317 : Nat := 4983230072969 + 3 ^ 40 * 7309317 * 2
def baseEnd_7309317 : Nat := 417021430786609333035841

theorem tailTrace_7309317 : CollatzResearch.WordTrace tailWord_7309317 prefixEnd_7309317 417021430786609333035841 := by
  unfold tailWord_7309317
  simp only [CollatzResearch.WordTrace]
  refine ⟨266592692460600315803926205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177728461640400210535950803 266592692460600315803926205)
  ·
    refine ⟨99972259672725118426472327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266592692460600315803926205 99972259672725118426472327)
    ·
      refine ⟨149958389509087677639708491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99972259672725118426472327 149958389509087677639708491)
      ·
        refine ⟨224937584263631516459562737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149958389509087677639708491 224937584263631516459562737)
        ·
          refine ⟨168703188197723637344672053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224937584263631516459562737 168703188197723637344672053)
          ·
            refine ⟨15815923893536591001063005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168703188197723637344672053 15815923893536591001063005)
            ·
              refine ⟨5930971460076221625398627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15815923893536591001063005 5930971460076221625398627)
              ·
                refine ⟨8896457190114332438097941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930971460076221625398627 8896457190114332438097941)
                ·
                  refine ⟨417021430786609333035841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8896457190114332438097941 417021430786609333035841)
                  ·
                    rfl

theorem cell23_7309317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_7309317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309317 prefixEnd_7309317 := by exact prefixLift 7309317
  have htrace : WordTrace (prefixWord ++ tailWord_7309317) baseStart_7309317 baseEnd_7309317 := by
    simpa [prefixWord, tailWord_7309317, baseEnd_7309317] using wordTrace_append hprefix tailTrace_7309317
  have hstable : (prefixWord ++ tailWord_7309317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309317).length < 2 ^ (prefixWord ++ tailWord_7309317).sum := by decide
  have hdescent : baseEnd_7309317 < baseStart_7309317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309337 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 2, 3, 2]
def baseStart_7309337 : Nat := 118140960795 + 7309337 * 2 ^ 59
def prefixEnd_7309337 : Nat := 4983230072969 + 3 ^ 40 * 7309337 * 2
def baseEnd_7309337 : Nat := 3753203146692573919072477

theorem tailTrace_7309337 : CollatzResearch.WordTrace tailWord_7309337 prefixEnd_7309337 3753203146692573919072477 := by
  unfold tailWord_7309337
  simp only [CollatzResearch.WordTrace]
  refine ⟨266593421920527859219654265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177728947947018572813102843 266593421920527859219654265)
  ·
    refine ⟨199945066440395894414740699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266593421920527859219654265 199945066440395894414740699)
    ·
      refine ⟨299917599660593841622111049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199945066440395894414740699 299917599660593841622111049)
      ·
        refine ⟨224938199745445381216583287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299917599660593841622111049 224938199745445381216583287)
        ·
          refine ⟨337407299618168071824874931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224938199745445381216583287 337407299618168071824874931)
          ·
            refine ⟨506110949427252107737312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337407299618168071824874931 506110949427252107737312397)
            ·
              refine ⟨189791606035219540401492149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506110949427252107737312397 189791606035219540401492149)
              ·
                refine ⟨17792963065801831912639889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189791606035219540401492149 17792963065801831912639889)
                ·
                  refine ⟨13344722299351373934479917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17792963065801831912639889 13344722299351373934479917)
                  ·
                    refine ⟨5004270862256765225429969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13344722299351373934479917 5004270862256765225429969)
                    ·
                      refine ⟨3753203146692573919072477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004270862256765225429969 3753203146692573919072477)
                      ·
                        rfl

theorem cell23_7309337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_7309337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309337 prefixEnd_7309337 := by exact prefixLift 7309337
  have htrace : WordTrace (prefixWord ++ tailWord_7309337) baseStart_7309337 baseEnd_7309337 := by
    simpa [prefixWord, tailWord_7309337, baseEnd_7309337] using wordTrace_append hprefix tailTrace_7309337
  have hstable : (prefixWord ++ tailWord_7309337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309337).length < 2 ^ (prefixWord ++ tailWord_7309337).sum := by decide
  have hdescent : baseEnd_7309337 < baseStart_7309337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309354 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7309354 : Nat := 118140960795 + 7309354 * 2 ^ 59
def prefixEnd_7309354 : Nat := 4983230072969 + 3 ^ 40 * 7309354 * 2
def baseEnd_7309354 : Nat := 3753211875863700352559899

theorem tailTrace_7309354 : CollatzResearch.WordTrace tailWord_7309354 prefixEnd_7309354 3753211875863700352559899 := by
  unfold tailWord_7309354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66648510490366567780755779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177729361307644180748682077 66648510490366567780755779)
  ·
    refine ⟨99972765735549851671133669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66648510490366567780755779 99972765735549851671133669)
    ·
      refine ⟨18744893575415597188337563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99972765735549851671133669 18744893575415597188337563)
      ·
        refine ⟨28117340363123395782506345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744893575415597188337563 28117340363123395782506345)
        ·
          refine ⟨21088005272342546836879759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28117340363123395782506345 21088005272342546836879759)
          ·
            refine ⟨31632007908513820255319639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21088005272342546836879759 31632007908513820255319639)
            ·
              refine ⟨47448011862770730382979459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31632007908513820255319639 47448011862770730382979459)
              ·
                refine ⟨71172017794156095574469189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47448011862770730382979459 71172017794156095574469189)
                ·
                  refine ⟨13344753336404267920212973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71172017794156095574469189 13344753336404267920212973)
                  ·
                    refine ⟨5004282501151600470079865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13344753336404267920212973 5004282501151600470079865)
                    ·
                      refine ⟨3753211875863700352559899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004282501151600470079865 3753211875863700352559899)
                      ·
                        rfl

theorem cell23_7309354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7309354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309354 prefixEnd_7309354 := by exact prefixLift 7309354
  have htrace : WordTrace (prefixWord ++ tailWord_7309354) baseStart_7309354 baseEnd_7309354 := by
    simpa [prefixWord, tailWord_7309354, baseEnd_7309354] using wordTrace_append hprefix tailTrace_7309354
  have hstable : (prefixWord ++ tailWord_7309354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309354).length < 2 ^ (prefixWord ++ tailWord_7309354).sum := by decide
  have hdescent : baseEnd_7309354 < baseStart_7309354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309370 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_7309370 : Nat := 118140960795 + 7309370 * 2 ^ 59
def prefixEnd_7309370 : Nat := 4983230072969 + 3 ^ 40 * 7309370 * 2
def baseEnd_7309370 : Nat := 3753220091554172289959825

theorem tailTrace_7309370 : CollatzResearch.WordTrace tailWord_7309370 prefixEnd_7309370 3753220091554172289959825 := by
  unfold tailWord_7309370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66648656382352076463901391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177729750352938870570403709 66648656382352076463901391)
  ·
    refine ⟨99972984573528114695852087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66648656382352076463901391 99972984573528114695852087)
    ·
      refine ⟨149959476860292172043778131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99972984573528114695852087 149959476860292172043778131)
      ·
        refine ⟨224939215290438258065667197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149959476860292172043778131 224939215290438258065667197)
        ·
          refine ⟨84352205733914346774625199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224939215290438258065667197 84352205733914346774625199)
          ·
            refine ⟨126528308600871520161937799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84352205733914346774625199 126528308600871520161937799)
            ·
              refine ⟨189792462901307280242906699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126528308600871520161937799 189792462901307280242906699)
              ·
                refine ⟨284688694351960920364360049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189792462901307280242906699 284688694351960920364360049)
                ·
                  refine ⟨213516520763970690273270037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284688694351960920364360049 213516520763970690273270037)
                  ·
                    refine ⟨10008586910811126106559533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213516520763970690273270037 10008586910811126106559533)
                    ·
                      refine ⟨3753220091554172289959825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008586910811126106559533 3753220091554172289959825)
                      ·
                        rfl

theorem cell23_7309370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_7309370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309370 prefixEnd_7309370 := by exact prefixLift 7309370
  have htrace : WordTrace (prefixWord ++ tailWord_7309370) baseStart_7309370 baseEnd_7309370 := by
    simpa [prefixWord, tailWord_7309370, baseEnd_7309370] using wordTrace_append hprefix tailTrace_7309370
  have hstable : (prefixWord ++ tailWord_7309370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309370).length < 2 ^ (prefixWord ++ tailWord_7309370).sum := by decide
  have hdescent : baseEnd_7309370 < baseStart_7309370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309390 : List Nat := [4, 1, 1, 1, 1, 4, 2, 9]
def baseStart_7309390 : Nat := 118140960795 + 7309390 * 2 ^ 59
def prefixEnd_7309390 : Nat := 4983230072969 + 3 ^ 40 * 7309390 * 2
def baseEnd_7309390 : Nat := 139008531895083785618879

theorem tailTrace_7309390 : CollatzResearch.WordTrace tailWord_7309390 prefixEnd_7309390 139008531895083785618879 := by
  unfold tailWord_7309390
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324419373666981158916703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177730236659557232847555749 33324419373666981158916703)
  ·
    refine ⟨49986629060500471738375055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33324419373666981158916703 49986629060500471738375055)
    ·
      refine ⟨74979943590750707607562583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49986629060500471738375055 74979943590750707607562583)
      ·
        refine ⟨112469915386126061411343875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74979943590750707607562583 112469915386126061411343875)
        ·
          refine ⟨168704873079189092117015813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112469915386126061411343875 168704873079189092117015813)
          ·
            refine ⟨31632163702347954771940465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168704873079189092117015813 31632163702347954771940465)
            ·
              refine ⟨23724122776760966078955349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31632163702347954771940465 23724122776760966078955349)
              ·
                refine ⟨139008531895083785618879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23724122776760966078955349 139008531895083785618879)
                ·
                  rfl

theorem cell23_7309390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_7309390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309390 prefixEnd_7309390 := by exact prefixLift 7309390
  have htrace : WordTrace (prefixWord ++ tailWord_7309390) baseStart_7309390 baseEnd_7309390 := by
    simpa [prefixWord, tailWord_7309390, baseEnd_7309390] using wordTrace_append hprefix tailTrace_7309390
  have hstable : (prefixWord ++ tailWord_7309390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309390).length < 2 ^ (prefixWord ++ tailWord_7309390).sum := by decide
  have hdescent : baseEnd_7309390 < baseStart_7309390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309397 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7309397 : Nat := 118140960795 + 7309397 * 2 ^ 59
def prefixEnd_7309397 : Nat := 4983230072969 + 3 ^ 40 * 7309397 * 2
def baseEnd_7309397 : Nat := 3753233955531843684322201

theorem tailTrace_7309397 : CollatzResearch.WordTrace tailWord_7309397 prefixEnd_7309397 3753233955531843684322201 := by
  unfold tailWord_7309397
  simp only [CollatzResearch.WordTrace]
  refine ⟨266595610300310489466838445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177730406866873659644558963 266595610300310489466838445)
  ·
    refine ⟨99973353862616433550064417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266595610300310489466838445 99973353862616433550064417)
    ·
      refine ⟨74980015396962325162548313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99973353862616433550064417 74980015396962325162548313)
      ·
        refine ⟨56235011547721743871911235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74980015396962325162548313 56235011547721743871911235)
        ·
          refine ⟨84352517321582615807866853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56235011547721743871911235 84352517321582615807866853)
          ·
            refine ⟨15816096997796740463975035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84352517321582615807866853 15816096997796740463975035)
            ·
              refine ⟨23724145496695110695962553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15816096997796740463975035 23724145496695110695962553)
              ·
                refine ⟨17793109122521333021971915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23724145496695110695962553 17793109122521333021971915)
                ·
                  refine ⟨26689663683781999532957873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17793109122521333021971915 26689663683781999532957873)
                  ·
                    refine ⟨20017247762836499649718405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26689663683781999532957873 20017247762836499649718405)
                    ·
                      refine ⟨3753233955531843684322201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20017247762836499649718405 3753233955531843684322201)
                      ·
                        rfl

theorem cell23_7309397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7309397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309397 prefixEnd_7309397 := by exact prefixLift 7309397
  have htrace : WordTrace (prefixWord ++ tailWord_7309397) baseStart_7309397 baseEnd_7309397 := by
    simpa [prefixWord, tailWord_7309397, baseEnd_7309397] using wordTrace_append hprefix tailTrace_7309397
  have hstable : (prefixWord ++ tailWord_7309397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309397).length < 2 ^ (prefixWord ++ tailWord_7309397).sum := by decide
  have hdescent : baseEnd_7309397 < baseStart_7309397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309398 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7309398 : Nat := 118140960795 + 7309398 * 2 ^ 59
def prefixEnd_7309398 : Nat := 4983230072969 + 3 ^ 40 * 7309398 * 2
def baseEnd_7309398 : Nat := 1251078156337499393469899

theorem tailTrace_7309398 : CollatzResearch.WordTrace tailWord_7309398 prefixEnd_7309398 1251078156337499393469899 := by
  unfold tailWord_7309398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662227923331679164851553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177730431182204577758416565 16662227923331679164851553)
  ·
    refine ⟨12496670942498759373638665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16662227923331679164851553 12496670942498759373638665)
    ·
      refine ⟨9372503206874069530228999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12496670942498759373638665 9372503206874069530228999)
      ·
        refine ⟨14058754810311104295343499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372503206874069530228999 14058754810311104295343499)
        ·
          refine ⟨21088132215466656443015249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058754810311104295343499 21088132215466656443015249)
          ·
            refine ⟨15816099161599992332261437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21088132215466656443015249 15816099161599992332261437)
            ·
              refine ⟨5931037185599997124598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15816099161599992332261437 5931037185599997124598039)
              ·
                refine ⟨8896555778399995686897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931037185599997124598039 8896555778399995686897059)
                ·
                  refine ⟨13344833667599993530345589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896555778399995686897059 13344833667599993530345589)
                  ·
                    refine ⟨1251078156337499393469899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13344833667599993530345589 1251078156337499393469899)
                    ·
                      rfl

theorem cell23_7309398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7309398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309398 prefixEnd_7309398 := by exact prefixLift 7309398
  have htrace : WordTrace (prefixWord ++ tailWord_7309398) baseStart_7309398 baseEnd_7309398 := by
    simpa [prefixWord, tailWord_7309398, baseEnd_7309398] using wordTrace_append hprefix tailTrace_7309398
  have hstable : (prefixWord ++ tailWord_7309398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309398).length < 2 ^ (prefixWord ++ tailWord_7309398).sum := by decide
  have hdescent : baseEnd_7309398 < baseStart_7309398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309401 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 1, 2, 2]
def baseStart_7309401 : Nat := 118140960795 + 7309401 * 2 ^ 59
def prefixEnd_7309401 : Nat := 4983230072969 + 3 ^ 40 * 7309401 * 2
def baseEnd_7309401 : Nat := 3753236009454461668672183

theorem tailTrace_7309401 : CollatzResearch.WordTrace tailWord_7309401 prefixEnd_7309401 3753236009454461668672183 := by
  unfold tailWord_7309401
  simp only [CollatzResearch.WordTrace]
  refine ⟨266595756192295998149984057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177730504128197332099989371 266595756192295998149984057)
  ·
    refine ⟨199946817144221998612488043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266595756192295998149984057 199946817144221998612488043)
    ·
      refine ⟨299920225716332997918732065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199946817144221998612488043 299920225716332997918732065)
      ·
        refine ⟨224940169287249748439049049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299920225716332997918732065 224940169287249748439049049)
        ·
          refine ⟨168705126965437311329286787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224940169287249748439049049 168705126965437311329286787)
          ·
            refine ⟨253057690448155966993930181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168705126965437311329286787 253057690448155966993930181)
            ·
              refine ⟨47448316959029243811361909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253057690448155966993930181 47448316959029243811361909)
              ·
                refine ⟨4448279714908991607315179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47448316959029243811361909 4448279714908991607315179)
                ·
                  refine ⟨6672419572363487410972769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448279714908991607315179 6672419572363487410972769)
                  ·
                    refine ⟨5004314679272615558229577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672419572363487410972769 5004314679272615558229577)
                    ·
                      refine ⟨3753236009454461668672183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004314679272615558229577 3753236009454461668672183)
                      ·
                        rfl

theorem cell23_7309401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_7309401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309401 prefixEnd_7309401 := by exact prefixLift 7309401
  have htrace : WordTrace (prefixWord ++ tailWord_7309401) baseStart_7309401 baseEnd_7309401 := by
    simpa [prefixWord, tailWord_7309401, baseEnd_7309401] using wordTrace_append hprefix tailTrace_7309401
  have hstable : (prefixWord ++ tailWord_7309401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309401).length < 2 ^ (prefixWord ++ tailWord_7309401).sum := by decide
  have hdescent : baseEnd_7309401 < baseStart_7309401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309404 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7309404 : Nat := 118140960795 + 7309404 * 2 ^ 59
def prefixEnd_7309404 : Nat := 4983230072969 + 3 ^ 40 * 7309404 * 2
def baseEnd_7309404 : Nat := 3753237549896425156934669

theorem tailTrace_7309404 : CollatzResearch.WordTrace tailWord_7309404 prefixEnd_7309404 3753237549896425156934669 := by
  unfold tailWord_7309404
  simp only [CollatzResearch.WordTrace]
  refine ⟨133297932805642564831171633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177730577074190086441562177 133297932805642564831171633)
  ·
    refine ⟨99973449604231923623378725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133297932805642564831171633 99973449604231923623378725)
    ·
      refine ⟨18745021800793485679383511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99973449604231923623378725 18745021800793485679383511)
      ·
        refine ⟨28117532701190228519075267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18745021800793485679383511 28117532701190228519075267)
        ·
          refine ⟨42176299051785342778612901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28117532701190228519075267 42176299051785342778612901)
          ·
            refine ⟨7908056072209751770989919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42176299051785342778612901 7908056072209751770989919)
            ·
              refine ⟨11862084108314627656484879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908056072209751770989919 11862084108314627656484879)
              ·
                refine ⟨17793126162471941484727319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862084108314627656484879 17793126162471941484727319)
                ·
                  refine ⟨26689689243707912227090979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17793126162471941484727319 26689689243707912227090979)
                  ·
                    refine ⟨40034533865561868340636469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26689689243707912227090979 40034533865561868340636469)
                    ·
                      refine ⟨3753237549896425156934669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40034533865561868340636469 3753237549896425156934669)
                      ·
                        rfl

theorem cell23_7309404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7309404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309404 prefixEnd_7309404 := by exact prefixLift 7309404
  have htrace : WordTrace (prefixWord ++ tailWord_7309404) baseStart_7309404 baseEnd_7309404 := by
    simpa [prefixWord, tailWord_7309404, baseEnd_7309404] using wordTrace_append hprefix tailTrace_7309404
  have hstable : (prefixWord ++ tailWord_7309404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309404).length < 2 ^ (prefixWord ++ tailWord_7309404).sum := by decide
  have hdescent : baseEnd_7309404 < baseStart_7309404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309420 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_7309420 : Nat := 118140960795 + 7309420 * 2 ^ 59
def prefixEnd_7309420 : Nat := 4983230072969 + 3 ^ 40 * 7309420 * 2
def baseEnd_7309420 : Nat := 1251081921862299031444865

theorem tailTrace_7309420 : CollatzResearch.WordTrace tailWord_7309420 prefixEnd_7309420 1251081921862299031444865 := by
  unfold tailWord_7309420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133298224589613582197462857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177730966119484776263283809 133298224589613582197462857)
  ·
    refine ⟨99973668442210186648097143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133298224589613582197462857 99973668442210186648097143)
    ·
      refine ⟨149960502663315279972145715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99973668442210186648097143 149960502663315279972145715)
      ·
        refine ⟨224940753994972919958218573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149960502663315279972145715 224940753994972919958218573)
        ·
          refine ⟨84352782748114844984331965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224940753994972919958218573 84352782748114844984331965)
          ·
            refine ⟨31632293530543066869124487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84352782748114844984331965 31632293530543066869124487)
            ·
              refine ⟨47448440295814600303686731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31632293530543066869124487 47448440295814600303686731)
              ·
                refine ⟨71172660443721900455530097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47448440295814600303686731 71172660443721900455530097)
                ·
                  refine ⟨53379495332791425341647573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71172660443721900455530097 53379495332791425341647573)
                  ·
                    refine ⟨1251081921862299031444865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53379495332791425341647573 1251081921862299031444865)
                    ·
                      rfl

theorem cell23_7309420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_7309420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309420 prefixEnd_7309420 := by exact prefixLift 7309420
  have htrace : WordTrace (prefixWord ++ tailWord_7309420) baseStart_7309420 baseEnd_7309420 := by
    simpa [prefixWord, tailWord_7309420, baseEnd_7309420] using wordTrace_append hprefix tailTrace_7309420
  have hstable : (prefixWord ++ tailWord_7309420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309420).length < 2 ^ (prefixWord ++ tailWord_7309420).sum := by decide
  have hdescent : baseEnd_7309420 < baseStart_7309420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309440 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_7309440 : Nat := 118140960795 + 7309440 * 2 ^ 59
def prefixEnd_7309440 : Nat := 4983230072969 + 3 ^ 40 * 7309440 * 2
def baseEnd_7309440 : Nat := 3753256035199987016084503

theorem tailTrace_7309440 : CollatzResearch.WordTrace tailWord_7309440 prefixEnd_7309440 3753256035199987016084503 := by
  unfold tailWord_7309440
  simp only [CollatzResearch.WordTrace]
  refine ⟨133298589319577353905326887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177731452426103138540435849 133298589319577353905326887)
  ·
    refine ⟨199947883979366030857990331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133298589319577353905326887 199947883979366030857990331)
    ·
      refine ⟨299921825969049046286985497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199947883979366030857990331 299921825969049046286985497)
      ·
        refine ⟨224941369476786784715239123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299921825969049046286985497 224941369476786784715239123)
        ·
          refine ⟨337412054215180177072858685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224941369476786784715239123 337412054215180177072858685)
          ·
            refine ⟨126529520330692566402322007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337412054215180177072858685 126529520330692566402322007)
            ·
              refine ⟨189794280496038849603483011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126529520330692566402322007 189794280496038849603483011)
              ·
                refine ⟨284691420744058274405224517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189794280496038849603483011 284691420744058274405224517)
                ·
                  refine ⟨53379641389510926450979597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284691420744058274405224517 53379641389510926450979597)
                  ·
                    refine ⟨20017365521066597419117349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53379641389510926450979597 20017365521066597419117349)
                    ·
                      refine ⟨3753256035199987016084503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20017365521066597419117349 3753256035199987016084503)
                      ·
                        rfl

theorem cell23_7309440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_7309440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309440 prefixEnd_7309440 := by exact prefixLift 7309440
  have htrace : WordTrace (prefixWord ++ tailWord_7309440) baseStart_7309440 baseEnd_7309440 := by
    simpa [prefixWord, tailWord_7309440, baseEnd_7309440] using wordTrace_append hprefix tailTrace_7309440
  have hstable : (prefixWord ++ tailWord_7309440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309440).length < 2 ^ (prefixWord ++ tailWord_7309440).sum := by decide
  have hdescent : baseEnd_7309440 < baseStart_7309440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309444 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_7309444 : Nat := 118140960795 + 7309444 * 2 ^ 59
def prefixEnd_7309444 : Nat := 4983230072969 + 3 ^ 40 * 7309444 * 2
def baseEnd_7309444 : Nat := 3753258089122605000434485

theorem tailTrace_7309444 : CollatzResearch.WordTrace tailWord_7309444 prefixEnd_7309444 3753258089122605000434485 := by
  unfold tailWord_7309444
  simp only [CollatzResearch.WordTrace]
  refine ⟨133298662265570108246899693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177731549687426810995866257 133298662265570108246899693)
  ·
    refine ⟨49986998349588790592587385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133298662265570108246899693 49986998349588790592587385)
    ·
      refine ⟨37490248762191592944440539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49986998349588790592587385 37490248762191592944440539)
      ·
        refine ⟨56235373143287389416660809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37490248762191592944440539 56235373143287389416660809)
        ·
          refine ⟨42176529857465542062495607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56235373143287389416660809 42176529857465542062495607)
          ·
            refine ⟨63264794786198313093743411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42176529857465542062495607 63264794786198313093743411)
            ·
              refine ⟨94897192179297469640615117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63264794786198313093743411 94897192179297469640615117)
              ·
                refine ⟨35586447067236551115230669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94897192179297469640615117 35586447067236551115230669)
                ·
                  refine ⟨13344917650213706668211501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35586447067236551115230669 13344917650213706668211501)
                  ·
                    refine ⟨5004344118830140000579313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13344917650213706668211501 5004344118830140000579313)
                    ·
                      refine ⟨3753258089122605000434485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004344118830140000579313 3753258089122605000434485)
                      ·
                        rfl

theorem cell23_7309444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_7309444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309444 prefixEnd_7309444 := by exact prefixLift 7309444
  have htrace : WordTrace (prefixWord ++ tailWord_7309444) baseStart_7309444 baseEnd_7309444 := by
    simpa [prefixWord, tailWord_7309444, baseEnd_7309444] using wordTrace_append hprefix tailTrace_7309444
  have hstable : (prefixWord ++ tailWord_7309444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309444).length < 2 ^ (prefixWord ++ tailWord_7309444).sum := by decide
  have hdescent : baseEnd_7309444 < baseStart_7309444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309520 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_7309520 : Nat := 118140960795 + 7309520 * 2 ^ 59
def prefixEnd_7309520 : Nat := 4983230072969 + 3 ^ 40 * 7309520 * 2
def baseEnd_7309520 : Nat := 3753297113652346703084135

theorem tailTrace_7309520 : CollatzResearch.WordTrace tailWord_7309520 prefixEnd_7309520 3753297113652346703084135 := by
  unfold tailWord_7309520
  simp only [CollatzResearch.WordTrace]
  refine ⟨133300048239432440736783007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177733397652576587649044009 133300048239432440736783007)
  ·
    refine ⟨199950072359148661105174511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133300048239432440736783007 199950072359148661105174511)
    ·
      refine ⟨299925108538722991657761767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199950072359148661105174511 299925108538722991657761767)
      ·
        refine ⟨449887662808084487486642651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299925108538722991657761767 449887662808084487486642651)
        ·
          refine ⟨674831494212126731229963977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449887662808084487486642651 674831494212126731229963977)
          ·
            refine ⟨506123620659095048422472983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674831494212126731229963977 506123620659095048422472983)
            ·
              refine ⟨759185430988642572633709475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506123620659095048422472983 759185430988642572633709475)
              ·
                refine ⟨1138778146482963858950564213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759185430988642572633709475 1138778146482963858950564213)
                ·
                  refine ⟨106760451232777861776615395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138778146482963858950564213 106760451232777861776615395)
                  ·
                    refine ⟨160140676849166792664923093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106760451232777861776615395 160140676849166792664923093)
                    ·
                      refine ⟨3753297113652346703084135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160140676849166792664923093 3753297113652346703084135)
                      ·
                        rfl

theorem cell23_7309520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_7309520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309520 prefixEnd_7309520 := by exact prefixLift 7309520
  have htrace : WordTrace (prefixWord ++ tailWord_7309520) baseStart_7309520 baseEnd_7309520 := by
    simpa [prefixWord, tailWord_7309520, baseEnd_7309520] using wordTrace_append hprefix tailTrace_7309520
  have hstable : (prefixWord ++ tailWord_7309520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309520).length < 2 ^ (prefixWord ++ tailWord_7309520).sum := by decide
  have hdescent : baseEnd_7309520 < baseStart_7309520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309537 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7309537 : Nat := 118140960795 + 7309537 * 2 ^ 59
def prefixEnd_7309537 : Nat := 4983230072969 + 3 ^ 40 * 7309537 * 2
def baseEnd_7309537 : Nat := 3753305842823473136571557

theorem tailTrace_7309537 : CollatzResearch.WordTrace tailWord_7309537 prefixEnd_7309537 3753305842823473136571557 := by
  unfold tailWord_7309537
  simp only [CollatzResearch.WordTrace]
  refine ⟨266600716519803293376934865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177733811013202195584623243 266600716519803293376934865)
  ·
    refine ⟨199950537389852470032701149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266600716519803293376934865 199950537389852470032701149)
    ·
      refine ⟨74981451521194676262262931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199950537389852470032701149 74981451521194676262262931)
      ·
        refine ⟨112472177281792014393394397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74981451521194676262262931 112472177281792014393394397)
        ·
          refine ⟨42177066480672005397522899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112472177281792014393394397 42177066480672005397522899)
          ·
            refine ⟨63265599721008008096284349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42177066480672005397522899 63265599721008008096284349)
            ·
              refine ⟨23724599895378003036106631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63265599721008008096284349 23724599895378003036106631)
              ·
                refine ⟨35586899843067004554159947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23724599895378003036106631 35586899843067004554159947)
                ·
                  refine ⟨53380349764600506831239921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35586899843067004554159947 53380349764600506831239921)
                  ·
                    refine ⟨40035262323450380123429941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53380349764600506831239921 40035262323450380123429941)
                    ·
                      refine ⟨3753305842823473136571557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40035262323450380123429941 3753305842823473136571557)
                      ·
                        rfl

theorem cell23_7309537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7309537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309537 prefixEnd_7309537 := by exact prefixLift 7309537
  have htrace : WordTrace (prefixWord ++ tailWord_7309537) baseStart_7309537 baseEnd_7309537 := by
    simpa [prefixWord, tailWord_7309537, baseEnd_7309537] using wordTrace_append hprefix tailTrace_7309537
  have hstable : (prefixWord ++ tailWord_7309537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309537).length < 2 ^ (prefixWord ++ tailWord_7309537).sum := by decide
  have hdescent : baseEnd_7309537 < baseStart_7309537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309547 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4]
def baseStart_7309547 : Nat := 118140960795 + 7309547 * 2 ^ 59
def prefixEnd_7309547 : Nat := 4983230072969 + 3 ^ 40 * 7309547 * 2
def baseEnd_7309547 : Nat := 3753310977630018097446511

theorem tailTrace_7309547 : CollatzResearch.WordTrace tailWord_7309547 prefixEnd_7309547 3753310977630018097446511 := by
  unfold tailWord_7309547
  simp only [CollatzResearch.WordTrace]
  refine ⟨266601081249767065084798895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177734054166511376723199263 266601081249767065084798895)
  ·
    refine ⟨399901621874650597627198343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266601081249767065084798895 399901621874650597627198343)
    ·
      refine ⟨599852432811975896440797515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399901621874650597627198343 599852432811975896440797515)
      ·
        refine ⟨899778649217963844661196273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599852432811975896440797515 899778649217963844661196273)
        ·
          refine ⟨674833986913472883495897205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899778649217963844661196273 674833986913472883495897205)
          ·
            refine ⟨63265686273138082827740363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 674833986913472883495897205 63265686273138082827740363)
            ·
              refine ⟨94898529409707124241610545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63265686273138082827740363 94898529409707124241610545)
              ·
                refine ⟨71173897057280343181207909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94898529409707124241610545 71173897057280343181207909)
                ·
                  refine ⟨13345105698240064346476483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71173897057280343181207909 13345105698240064346476483)
                  ·
                    refine ⟨20017658547360096519714725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13345105698240064346476483 20017658547360096519714725)
                    ·
                      refine ⟨3753310977630018097446511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20017658547360096519714725 3753310977630018097446511)
                      ·
                        rfl

theorem cell23_7309547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_7309547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309547 prefixEnd_7309547 := by exact prefixLift 7309547
  have htrace : WordTrace (prefixWord ++ tailWord_7309547) baseStart_7309547 baseEnd_7309547 := by
    simpa [prefixWord, tailWord_7309547, baseEnd_7309547] using wordTrace_append hprefix tailTrace_7309547
  have hstable : (prefixWord ++ tailWord_7309547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309547).length < 2 ^ (prefixWord ++ tailWord_7309547).sum := by decide
  have hdescent : baseEnd_7309547 < baseStart_7309547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309564 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7309564 : Nat := 118140960795 + 7309564 * 2 ^ 59
def prefixEnd_7309564 : Nat := 4983230072969 + 3 ^ 40 * 7309564 * 2
def baseEnd_7309564 : Nat := 3753319706801144530933933

theorem tailTrace_7309564 : CollatzResearch.WordTrace tailWord_7309564 prefixEnd_7309564 3753319706801144530933933 := by
  unfold tailWord_7309564
  simp only [CollatzResearch.WordTrace]
  refine ⟨133300850645352738494083873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177734467527136984658778497 133300850645352738494083873)
  ·
    refine ⟨99975637984014553870562905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133300850645352738494083873 99975637984014553870562905)
    ·
      refine ⟨74981728488010915402922179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99975637984014553870562905 74981728488010915402922179)
      ·
        refine ⟨112472592732016373104383269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74981728488010915402922179 112472592732016373104383269)
        ·
          refine ⟨21088611137253069957071863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112472592732016373104383269 21088611137253069957071863)
          ·
            refine ⟨31632916705879604935607795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21088611137253069957071863 31632916705879604935607795)
            ·
              refine ⟨47449375058819407403411693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31632916705879604935607795 47449375058819407403411693)
              ·
                refine ⟨17793515647057277776279385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47449375058819407403411693 17793515647057277776279385)
                ·
                  refine ⟨13345136735292958332209539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17793515647057277776279385 13345136735292958332209539)
                  ·
                    refine ⟨20017705102939437498314309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13345136735292958332209539 20017705102939437498314309)
                    ·
                      refine ⟨3753319706801144530933933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20017705102939437498314309 3753319706801144530933933)
                      ·
                        rfl

theorem cell23_7309564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7309564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309564 prefixEnd_7309564 := by exact prefixLift 7309564
  have htrace : WordTrace (prefixWord ++ tailWord_7309564) baseStart_7309564 baseEnd_7309564 := by
    simpa [prefixWord, tailWord_7309564, baseEnd_7309564] using wordTrace_append hprefix tailTrace_7309564
  have hstable : (prefixWord ++ tailWord_7309564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309564).length < 2 ^ (prefixWord ++ tailWord_7309564).sum := by decide
  have hdescent : baseEnd_7309564 < baseStart_7309564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309598 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7309598 : Nat := 118140960795 + 7309598 * 2 ^ 59
def prefixEnd_7309598 : Nat := 4983230072969 + 3 ^ 40 * 7309598 * 2
def baseEnd_7309598 : Nat := 3753337165143397397908777

theorem tailTrace_7309598 : CollatzResearch.WordTrace tailWord_7309598 prefixEnd_7309598 3753337165143397397908777 := by
  unfold tailWord_7309598
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325367671572787599363181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177735294248388200529936965 33325367671572787599363181)
  ·
    refine ⟨12497012876839795349761193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33325367671572787599363181 12497012876839795349761193)
    ·
      refine ⟨9372759657629846512320895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497012876839795349761193 9372759657629846512320895)
      ·
        refine ⟨14059139486444769768481343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372759657629846512320895 14059139486444769768481343)
        ·
          refine ⟨21088709229667154652722015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059139486444769768481343 21088709229667154652722015)
          ·
            refine ⟨31633063844500731979083023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21088709229667154652722015 31633063844500731979083023)
            ·
              refine ⟨47449595766751097968624535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31633063844500731979083023 47449595766751097968624535)
              ·
                refine ⟨71174393650126646952936803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47449595766751097968624535 71174393650126646952936803)
                ·
                  refine ⟨106761590475189970429405205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71174393650126646952936803 106761590475189970429405205)
                  ·
                    refine ⟨5004449553524529863878369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106761590475189970429405205 5004449553524529863878369)
                    ·
                      refine ⟨3753337165143397397908777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004449553524529863878369 3753337165143397397908777)
                      ·
                        rfl

theorem cell23_7309598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7309598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309598 prefixEnd_7309598 := by exact prefixLift 7309598
  have htrace : WordTrace (prefixWord ++ tailWord_7309598) baseStart_7309598 baseEnd_7309598 := by
    simpa [prefixWord, tailWord_7309598, baseEnd_7309598] using wordTrace_append hprefix tailTrace_7309598
  have hstable : (prefixWord ++ tailWord_7309598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309598).length < 2 ^ (prefixWord ++ tailWord_7309598).sum := by decide
  have hdescent : baseEnd_7309598 < baseStart_7309598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309604 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 6]
def baseStart_7309604 : Nat := 118140960795 + 7309604 * 2 ^ 59
def prefixEnd_7309604 : Nat := 4983230072969 + 3 ^ 40 * 7309604 * 2
def baseEnd_7309604 : Nat := 417037805114147152714861

theorem tailTrace_7309604 : CollatzResearch.WordTrace tailWord_7309604 prefixEnd_7309604 417037805114147152714861 := by
  unfold tailWord_7309604
  simp only [CollatzResearch.WordTrace]
  refine ⟨133301580105280281909811933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177735440140373709213082577 133301580105280281909811933)
  ·
    refine ⟨49988092539480105716179475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133301580105280281909811933 49988092539480105716179475)
    ·
      refine ⟨74982138809220158574269213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49988092539480105716179475 74982138809220158574269213)
      ·
        refine ⟨28118302053457559465350955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74982138809220158574269213 28118302053457559465350955)
        ·
          refine ⟨42177453080186339198026433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28118302053457559465350955 42177453080186339198026433)
          ·
            refine ⟨31633089810139754398519825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42177453080186339198026433 31633089810139754398519825)
            ·
              refine ⟨23724817357604815798889869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31633089810139754398519825 23724817357604815798889869)
              ·
                refine ⟨8896806509101805924583701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23724817357604815798889869 8896806509101805924583701)
                ·
                  refine ⟨417037805114147152714861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8896806509101805924583701 417037805114147152714861)
                  ·
                    rfl

theorem cell23_7309604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_7309604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309604 prefixEnd_7309604 := by exact prefixLift 7309604
  have htrace : WordTrace (prefixWord ++ tailWord_7309604) baseStart_7309604 baseEnd_7309604 := by
    simpa [prefixWord, tailWord_7309604, baseEnd_7309604] using wordTrace_append hprefix tailTrace_7309604
  have hstable : (prefixWord ++ tailWord_7309604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309604).length < 2 ^ (prefixWord ++ tailWord_7309604).sum := by decide
  have hdescent : baseEnd_7309604 < baseStart_7309604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309618 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_7309618 : Nat := 118140960795 + 7309618 * 2 ^ 59
def prefixEnd_7309618 : Nat := 4983230072969 + 3 ^ 40 * 7309618 * 2
def baseEnd_7309618 : Nat := 3753347434756487319658685

theorem tailTrace_7309618 : CollatzResearch.WordTrace tailWord_7309618 prefixEnd_7309618 3753347434756487319658685 := by
  unfold tailWord_7309618
  simp only [CollatzResearch.WordTrace]
  refine ⟨66650917708127461052658377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177735780555006562807089005 66650917708127461052658377)
  ·
    refine ⟨49988188281095595789493783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66650917708127461052658377 49988188281095595789493783)
    ·
      refine ⟨74982282421643393684240675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49988188281095595789493783 74982282421643393684240675)
      ·
        refine ⟨112473423632465090526361013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74982282421643393684240675 112473423632465090526361013)
        ·
          refine ⟨10544383465543602236846345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112473423632465090526361013 10544383465543602236846345)
          ·
            refine ⟨7908287599157701677634759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544383465543602236846345 7908287599157701677634759)
            ·
              refine ⟨11862431398736552516452139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908287599157701677634759 11862431398736552516452139)
              ·
                refine ⟨17793647098104828774678209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862431398736552516452139 17793647098104828774678209)
                ·
                  refine ⟨13345235323578621581008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17793647098104828774678209 13345235323578621581008657)
                  ·
                    refine ⟨10008926492683966185756493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13345235323578621581008657 10008926492683966185756493)
                    ·
                      refine ⟨3753347434756487319658685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008926492683966185756493 3753347434756487319658685)
                      ·
                        rfl

theorem cell23_7309618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_7309618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309618 prefixEnd_7309618 := by exact prefixLift 7309618
  have htrace : WordTrace (prefixWord ++ tailWord_7309618) baseStart_7309618 baseEnd_7309618 := by
    simpa [prefixWord, tailWord_7309618, baseEnd_7309618] using wordTrace_append hprefix tailTrace_7309618
  have hstable : (prefixWord ++ tailWord_7309618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309618).length < 2 ^ (prefixWord ++ tailWord_7309618).sum := by decide
  have hdescent : baseEnd_7309618 < baseStart_7309618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309648 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 1, 1, 3]
def baseStart_7309648 : Nat := 118140960795 + 7309648 * 2 ^ 59
def prefixEnd_7309648 : Nat := 4983230072969 + 3 ^ 40 * 7309648 * 2
def baseEnd_7309648 : Nat := 3753362839176122202283547

theorem tailTrace_7309648 : CollatzResearch.WordTrace tailWord_7309648 prefixEnd_7309648 3753362839176122202283547 := by
  unfold tailWord_7309648
  simp only [CollatzResearch.WordTrace]
  refine ⟨133302382511200579667112799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177736510014934106222817065 133302382511200579667112799)
  ·
    refine ⟨199953573766800869500669199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133302382511200579667112799 199953573766800869500669199)
    ·
      refine ⟨299930360650201304251003799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199953573766800869500669199 299930360650201304251003799)
      ·
        refine ⟨449895540975301956376505699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299930360650201304251003799 449895540975301956376505699)
        ·
          refine ⟨674843311462952934564758549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449895540975301956376505699 674843311462952934564758549)
          ·
            refine ⟨31633280224825918807723057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 674843311462952934564758549 31633280224825918807723057)
            ·
              refine ⟨23724960168619439105792293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31633280224825918807723057 23724960168619439105792293)
              ·
                refine ⟨4448430031616144832336055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23724960168619439105792293 4448430031616144832336055)
                ·
                  refine ⟨6672645047424217248504083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448430031616144832336055 6672645047424217248504083)
                  ·
                    refine ⟨10008967571136325872756125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6672645047424217248504083 10008967571136325872756125)
                    ·
                      refine ⟨3753362839176122202283547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10008967571136325872756125 3753362839176122202283547)
                      ·
                        rfl

theorem cell23_7309648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 1, 3].length) (baseStart_7309648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309648 prefixEnd_7309648 := by exact prefixLift 7309648
  have htrace : WordTrace (prefixWord ++ tailWord_7309648) baseStart_7309648 baseEnd_7309648 := by
    simpa [prefixWord, tailWord_7309648, baseEnd_7309648] using wordTrace_append hprefix tailTrace_7309648
  have hstable : (prefixWord ++ tailWord_7309648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309648).length < 2 ^ (prefixWord ++ tailWord_7309648).sum := by decide
  have hdescent : baseEnd_7309648 < baseStart_7309648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309671 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_7309671 : Nat := 118140960795 + 7309671 * 2 ^ 59
def prefixEnd_7309671 : Nat := 4983230072969 + 3 ^ 40 * 7309671 * 2
def baseEnd_7309671 : Nat := 3753374649231175612295941

theorem tailTrace_7309671 : CollatzResearch.WordTrace tailWord_7309671 prefixEnd_7309671 3753374649231175612295941 := by
  unfold tailWord_7309671
  simp only [CollatzResearch.WordTrace]
  refine ⟨266605603901317834262312867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177737069267545222841541911 266605603901317834262312867)
  ·
    refine ⟨399908405851976751393469301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266605603901317834262312867 399908405851976751393469301)
    ·
      refine ⟨37491413048622820443137747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399908405851976751393469301 37491413048622820443137747)
      ·
        refine ⟨56237119572934230664706621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37491413048622820443137747 56237119572934230664706621)
        ·
          refine ⟨21088919839850336499264983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56237119572934230664706621 21088919839850336499264983)
          ·
            refine ⟨31633379759775504748897475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21088919839850336499264983 31633379759775504748897475)
            ·
              refine ⟨47450069639663257123346213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31633379759775504748897475 47450069639663257123346213)
              ·
                refine ⟨8896888057436860710627415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47450069639663257123346213 8896888057436860710627415)
                ·
                  refine ⟨13345332086155291065941123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896888057436860710627415 13345332086155291065941123)
                  ·
                    refine ⟨20017998129232936598911685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13345332086155291065941123 20017998129232936598911685)
                    ·
                      refine ⟨3753374649231175612295941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20017998129232936598911685 3753374649231175612295941)
                      ·
                        rfl

theorem cell23_7309671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_7309671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309671 prefixEnd_7309671 := by exact prefixLift 7309671
  have htrace : WordTrace (prefixWord ++ tailWord_7309671) baseStart_7309671 baseEnd_7309671 := by
    simpa [prefixWord, tailWord_7309671, baseEnd_7309671] using wordTrace_append hprefix tailTrace_7309671
  have hstable : (prefixWord ++ tailWord_7309671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309671).length < 2 ^ (prefixWord ++ tailWord_7309671).sum := by decide
  have hdescent : baseEnd_7309671 < baseStart_7309671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309691 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 3]
def baseStart_7309691 : Nat := 118140960795 + 7309691 * 2 ^ 59
def prefixEnd_7309691 : Nat := 4983230072969 + 3 ^ 40 * 7309691 * 2
def baseEnd_7309691 : Nat := 3753384918844265534045849

theorem tailTrace_7309691 : CollatzResearch.WordTrace tailWord_7309691 prefixEnd_7309691 3753384918844265534045849 := by
  unfold tailWord_7309691
  simp only [CollatzResearch.WordTrace]
  refine ⟨266606333361245377678040927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177737555574163585118693951 266606333361245377678040927)
  ·
    refine ⟨399909500041868066517061391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266606333361245377678040927 399909500041868066517061391)
    ·
      refine ⟨599864250062802099775592087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399909500041868066517061391 599864250062802099775592087)
      ·
        refine ⟨899796375094203149663388131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599864250062802099775592087 899796375094203149663388131)
        ·
          refine ⟨1349694562641304724495082197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899796375094203149663388131 1349694562641304724495082197)
          ·
            refine ⟨31633466311905579480353489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1349694562641304724495082197 31633466311905579480353489)
            ·
              refine ⟨23725099733929184610265117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31633466311905579480353489 23725099733929184610265117)
              ·
                refine ⟨8896912400223444228849419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23725099733929184610265117 8896912400223444228849419)
                ·
                  refine ⟨13345368600335166343274129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896912400223444228849419 13345368600335166343274129)
                  ·
                    refine ⟨10009026450251374757455597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13345368600335166343274129 10009026450251374757455597)
                    ·
                      refine ⟨3753384918844265534045849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10009026450251374757455597 3753384918844265534045849)
                      ·
                        rfl

theorem cell23_7309691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 3].length) (baseStart_7309691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309691 prefixEnd_7309691 := by exact prefixLift 7309691
  have htrace : WordTrace (prefixWord ++ tailWord_7309691) baseStart_7309691 baseEnd_7309691 := by
    simpa [prefixWord, tailWord_7309691, baseEnd_7309691] using wordTrace_append hprefix tailTrace_7309691
  have hstable : (prefixWord ++ tailWord_7309691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309691).length < 2 ^ (prefixWord ++ tailWord_7309691).sum := by decide
  have hdescent : baseEnd_7309691 < baseStart_7309691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309705 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 3, 2, 2]
def baseStart_7309705 : Nat := 118140960795 + 7309705 * 2 ^ 59
def prefixEnd_7309705 : Nat := 4983230072969 + 3 ^ 40 * 7309705 * 2
def baseEnd_7309705 : Nat := 3753392107573428479270785

theorem tailTrace_7309705 : CollatzResearch.WordTrace tailWord_7309705 prefixEnd_7309705 3753392107573428479270785 := by
  unfold tailWord_7309705
  simp only [CollatzResearch.WordTrace]
  refine ⟨266606843983194658069050569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177737895988796438712700379 266606843983194658069050569)
  ·
    refine ⟨199955132987395993551787927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266606843983194658069050569 199955132987395993551787927)
    ·
      refine ⟨299932699481093990327681891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199955132987395993551787927 299932699481093990327681891)
      ·
        refine ⟨449899049221640985491522837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299932699481093990327681891 449899049221640985491522837)
        ·
          refine ⟨21089017932264421194915133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 449899049221640985491522837 21089017932264421194915133)
          ·
            refine ⟨7908381724599157948093175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21089017932264421194915133 7908381724599157948093175)
            ·
              refine ⟨11862572586898736922139763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908381724599157948093175 11862572586898736922139763)
              ·
                refine ⟨17793858880348105383209645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862572586898736922139763 17793858880348105383209645)
                ·
                  refine ⟨6672697080130539518703617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17793858880348105383209645 6672697080130539518703617)
                  ·
                    refine ⟨5004522810097904639027713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672697080130539518703617 5004522810097904639027713)
                    ·
                      refine ⟨3753392107573428479270785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004522810097904639027713 3753392107573428479270785)
                      ·
                        rfl

theorem cell23_7309705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2, 2].length) (baseStart_7309705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309705 prefixEnd_7309705 := by exact prefixLift 7309705
  have htrace : WordTrace (prefixWord ++ tailWord_7309705) baseStart_7309705 baseEnd_7309705 := by
    simpa [prefixWord, tailWord_7309705, baseEnd_7309705] using wordTrace_append hprefix tailTrace_7309705
  have hstable : (prefixWord ++ tailWord_7309705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309705).length < 2 ^ (prefixWord ++ tailWord_7309705).sum := by decide
  have hdescent : baseEnd_7309705 < baseStart_7309705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309725 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_7309725 : Nat := 118140960795 + 7309725 * 2 ^ 59
def prefixEnd_7309725 : Nat := 4983230072969 + 3 ^ 40 * 7309725 * 2
def baseEnd_7309725 : Nat := 3753402377186518401020693

theorem tailTrace_7309725 : CollatzResearch.WordTrace tailWord_7309725 prefixEnd_7309725 3753402377186518401020693 := by
  unfold tailWord_7309725
  simp only [CollatzResearch.WordTrace]
  refine ⟨266607573443122201484778629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177738382295414800989852419 266607573443122201484778629)
  ·
    refine ⟨49988920020585412778395993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266607573443122201484778629 49988920020585412778395993)
    ·
      refine ⟨37491690015439059583796995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49988920020585412778395993 37491690015439059583796995)
      ·
        refine ⟨56237535023158589375695493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37491690015439059583796995 56237535023158589375695493)
        ·
          refine ⟨10544537816842235507942905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56237535023158589375695493 10544537816842235507942905)
          ·
            refine ⟨7908403362631676630957179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544537816842235507942905 7908403362631676630957179)
            ·
              refine ⟨11862605043947514946435769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908403362631676630957179 11862605043947514946435769)
              ·
                refine ⟨8896953782960636209826827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862605043947514946435769 8896953782960636209826827)
                ·
                  refine ⟨13345430674440954314740241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896953782960636209826827 13345430674440954314740241)
                  ·
                    refine ⟨10009073005830715736055181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13345430674440954314740241 10009073005830715736055181)
                    ·
                      refine ⟨3753402377186518401020693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10009073005830715736055181 3753402377186518401020693)
                      ·
                        rfl

theorem cell23_7309725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_7309725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309725 prefixEnd_7309725 := by exact prefixLift 7309725
  have htrace : WordTrace (prefixWord ++ tailWord_7309725) baseStart_7309725 baseEnd_7309725 := by
    simpa [prefixWord, tailWord_7309725, baseEnd_7309725] using wordTrace_append hprefix tailTrace_7309725
  have hstable : (prefixWord ++ tailWord_7309725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309725).length < 2 ^ (prefixWord ++ tailWord_7309725).sum := by decide
  have hdescent : baseEnd_7309725 < baseStart_7309725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309828 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7309828 : Nat := 118140960795 + 7309828 * 2 ^ 59
def prefixEnd_7309828 : Nat := 4983230072969 + 3 ^ 40 * 7309828 * 2
def baseEnd_7309828 : Nat := 3753455265693931498032719

theorem tailTrace_7309828 : CollatzResearch.WordTrace tailWord_7309828 prefixEnd_7309828 3753455265693931498032719 := by
  unfold tailWord_7309828
  simp only [CollatzResearch.WordTrace]
  refine ⟨133305665080874525037889069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177740886774499366717185425 133305665080874525037889069)
  ·
    refine ⟨49989624405327946889208401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133305665080874525037889069 49989624405327946889208401)
    ·
      refine ⟨37492218303995960166906301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49989624405327946889208401 37492218303995960166906301)
      ·
        refine ⟨14059581863998485062589863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37492218303995960166906301 14059581863998485062589863)
        ·
          refine ⟨21089372795997727593884795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059581863998485062589863 21089372795997727593884795)
          ·
            refine ⟨31634059193996591390827193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089372795997727593884795 31634059193996591390827193)
            ·
              refine ⟨23725544395497443543120395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31634059193996591390827193 23725544395497443543120395)
              ·
                refine ⟨35588316593246165314680593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23725544395497443543120395 35588316593246165314680593)
                ·
                  refine ⟨26691237444934623986010445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35588316593246165314680593 26691237444934623986010445)
                  ·
                    refine ⟨10009214041850483994753917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26691237444934623986010445 10009214041850483994753917)
                    ·
                      refine ⟨3753455265693931498032719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10009214041850483994753917 3753455265693931498032719)
                      ·
                        rfl

theorem cell23_7309828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7309828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309828 prefixEnd_7309828 := by exact prefixLift 7309828
  have htrace : WordTrace (prefixWord ++ tailWord_7309828) baseStart_7309828 baseEnd_7309828 := by
    simpa [prefixWord, tailWord_7309828, baseEnd_7309828] using wordTrace_append hprefix tailTrace_7309828
  have hstable : (prefixWord ++ tailWord_7309828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309828).length < 2 ^ (prefixWord ++ tailWord_7309828).sum := by decide
  have hdescent : baseEnd_7309828 < baseStart_7309828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309861 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_7309861 : Nat := 118140960795 + 7309861 * 2 ^ 59
def prefixEnd_7309861 : Nat := 4983230072969 + 3 ^ 40 * 7309861 * 2
def baseEnd_7309861 : Nat := 1251157403518509956306689

theorem tailTrace_7309861 : CollatzResearch.WordTrace tailWord_7309861 prefixEnd_7309861 1251157403518509956306689 := by
  unfold tailWord_7309861
  simp only [CollatzResearch.WordTrace]
  refine ⟨266612533770629496711729437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177741689180419664474486291 266612533770629496711729437)
  ·
    refine ⟨99979700163986061266898539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266612533770629496711729437 99979700163986061266898539)
    ·
      refine ⟨149969550245979091900347809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99979700163986061266898539 149969550245979091900347809)
      ·
        refine ⟨112477162684484318925260857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149969550245979091900347809 112477162684484318925260857)
        ·
          refine ⟨84357872013363239193945643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112477162684484318925260857 84357872013363239193945643)
          ·
            refine ⟨126536808020044858790918465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84357872013363239193945643 126536808020044858790918465)
            ·
              refine ⟨94902606015033644093188849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126536808020044858790918465 94902606015033644093188849)
              ·
                refine ⟨71176954511275233069891637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94902606015033644093188849 71176954511275233069891637)
                ·
                  refine ⟨6672839485432053100302341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71176954511275233069891637 6672839485432053100302341)
                  ·
                    refine ⟨1251157403518509956306689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672839485432053100302341 1251157403518509956306689)
                    ·
                      rfl

theorem cell23_7309861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_7309861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309861 prefixEnd_7309861 := by exact prefixLift 7309861
  have htrace : WordTrace (prefixWord ++ tailWord_7309861) baseStart_7309861 baseEnd_7309861 := by
    simpa [prefixWord, tailWord_7309861, baseEnd_7309861] using wordTrace_append hprefix tailTrace_7309861
  have hstable : (prefixWord ++ tailWord_7309861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309861).length < 2 ^ (prefixWord ++ tailWord_7309861).sum := by decide
  have hdescent : baseEnd_7309861 < baseStart_7309861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309869 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 7]
def baseStart_7309869 : Nat := 118140960795 + 7309869 * 2 ^ 59
def prefixEnd_7309869 : Nat := 4983230072969 + 3 ^ 40 * 7309869 * 2
def baseEnd_7309869 : Nat := 417052924266751759735559

theorem tailTrace_7309869 : CollatzResearch.WordTrace tailWord_7309869 prefixEnd_7309869 417052924266751759735559 := by
  unfold tailWord_7309869
  simp only [CollatzResearch.WordTrace]
  refine ⟨266612825554600514078020661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177741883703067009385347107 266612825554600514078020661)
  ·
    refine ⟨24994952395743798194814437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266612825554600514078020661 24994952395743798194814437)
    ·
      refine ⟨4686553574201962161527707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24994952395743798194814437 4686553574201962161527707)
      ·
        refine ⟨7029830361302943242291561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686553574201962161527707 7029830361302943242291561)
        ·
          refine ⟨5272372770977207431718671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7029830361302943242291561 5272372770977207431718671)
          ·
            refine ⟨7908559156465811147578007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272372770977207431718671 7908559156465811147578007)
            ·
              refine ⟨11862838734698716721367011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908559156465811147578007 11862838734698716721367011)
              ·
                refine ⟨17794258102048075082050517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862838734698716721367011 17794258102048075082050517)
                ·
                  refine ⟨417052924266751759735559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17794258102048075082050517 417052924266751759735559)
                  ·
                    rfl

theorem cell23_7309869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_7309869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309869 prefixEnd_7309869 := by exact prefixLift 7309869
  have htrace : WordTrace (prefixWord ++ tailWord_7309869) baseStart_7309869 baseEnd_7309869 := by
    simpa [prefixWord, tailWord_7309869, baseEnd_7309869] using wordTrace_append hprefix tailTrace_7309869
  have hstable : (prefixWord ++ tailWord_7309869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309869).length < 2 ^ (prefixWord ++ tailWord_7309869).sum := by decide
  have hdescent : baseEnd_7309869 < baseStart_7309869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309972 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7309972 : Nat := 118140960795 + 7309972 * 2 ^ 59
def prefixEnd_7309972 : Nat := 4983230072969 + 3 ^ 40 * 7309972 * 2
def baseEnd_7309972 : Nat := 1251176402302726311544019

theorem tailTrace_7309972 : CollatzResearch.WordTrace tailWord_7309972 prefixEnd_7309972 1251176402302726311544019 := by
  unfold tailWord_7309972
  simp only [CollatzResearch.WordTrace]
  refine ⟨133308291136613681334510085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177744388182151575112680113 133308291136613681334510085)
  ·
    refine ⟨24995304588115065250220641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133308291136613681334510085 24995304588115065250220641)
    ·
      refine ⟨18746478441086298937665481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24995304588115065250220641 18746478441086298937665481)
      ·
        refine ⟨14059858830814724203249111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18746478441086298937665481 14059858830814724203249111)
        ·
          refine ⟨21089788246222086304873667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059858830814724203249111 21089788246222086304873667)
          ·
            refine ⟨31634682369333129457310501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089788246222086304873667 31634682369333129457310501)
            ·
              refine ⟨5931502944249961773245719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31634682369333129457310501 5931502944249961773245719)
              ·
                refine ⟨8897254416374942659868579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931502944249961773245719 8897254416374942659868579)
                ·
                  refine ⟨13345881624562413989802869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8897254416374942659868579 13345881624562413989802869)
                  ·
                    refine ⟨1251176402302726311544019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13345881624562413989802869 1251176402302726311544019)
                    ·
                      rfl

theorem cell23_7309972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7309972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309972 prefixEnd_7309972 := by exact prefixLift 7309972
  have htrace : WordTrace (prefixWord ++ tailWord_7309972) baseStart_7309972 baseEnd_7309972 := by
    simpa [prefixWord, tailWord_7309972, baseEnd_7309972] using wordTrace_append hprefix tailTrace_7309972
  have hstable : (prefixWord ++ tailWord_7309972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309972).length < 2 ^ (prefixWord ++ tailWord_7309972).sum := by decide
  have hdescent : baseEnd_7309972 < baseStart_7309972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309975 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_7309975 : Nat := 118140960795 + 7309975 * 2 ^ 59
def prefixEnd_7309975 : Nat := 4983230072969 + 3 ^ 40 * 7309975 * 2
def baseEnd_7309975 : Nat := 3753530747350142422894543

theorem tailTrace_7309975 : CollatzResearch.WordTrace tailWord_7309975 prefixEnd_7309975 3753530747350142422894543 := by
  unfold tailWord_7309975
  simp only [CollatzResearch.WordTrace]
  refine ⟨266616691692216494181379379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177744461128144329454252919 266616691692216494181379379)
  ·
    refine ⟨399925037538324741272069069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266616691692216494181379379 399925037538324741272069069)
    ·
      refine ⟨149971889076871777977025901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399925037538324741272069069 149971889076871777977025901)
      ·
        refine ⟨56239458403826916741384713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149971889076871777977025901 56239458403826916741384713)
        ·
          refine ⟨42179593802870187556038535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56239458403826916741384713 42179593802870187556038535)
          ·
            refine ⟨63269390704305281334057803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42179593802870187556038535 63269390704305281334057803)
            ·
              refine ⟨94904086056457922001086705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63269390704305281334057803 94904086056457922001086705)
              ·
                refine ⟨71178064542343441500815029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94904086056457922001086705 71178064542343441500815029)
                ·
                  refine ⟨6672943550844697640701409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71178064542343441500815029 6672943550844697640701409)
                  ·
                    refine ⟨5004707663133523230526057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672943550844697640701409 5004707663133523230526057)
                    ·
                      refine ⟨3753530747350142422894543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004707663133523230526057 3753530747350142422894543)
                      ·
                        rfl

theorem cell23_7309975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_7309975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309975 prefixEnd_7309975 := by exact prefixLift 7309975
  have htrace : WordTrace (prefixWord ++ tailWord_7309975) baseStart_7309975 baseEnd_7309975 := by
    simpa [prefixWord, tailWord_7309975, baseEnd_7309975] using wordTrace_append hprefix tailTrace_7309975
  have hstable : (prefixWord ++ tailWord_7309975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309975).length < 2 ^ (prefixWord ++ tailWord_7309975).sum := by decide
  have hdescent : baseEnd_7309975 < baseStart_7309975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7309985 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_7309985 : Nat := 118140960795 + 7309985 * 2 ^ 59
def prefixEnd_7309985 : Nat := 4983230072969 + 3 ^ 40 * 7309985 * 2
def baseEnd_7309985 : Nat := 1251178627385562461256499

theorem tailTrace_7309985 : CollatzResearch.WordTrace tailWord_7309985 prefixEnd_7309985 1251178627385562461256499 := by
  unfold tailWord_7309985
  simp only [CollatzResearch.WordTrace]
  refine ⟨266617056422180265889243409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177744704281453510592828939 266617056422180265889243409)
  ·
    refine ⟨199962792316635199416932557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266617056422180265889243409 199962792316635199416932557)
    ·
      refine ⟨74986047118738199781349709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199962792316635199416932557 74986047118738199781349709)
      ·
        refine ⟨28119767669526824918006141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74986047118738199781349709 28119767669526824918006141)
        ·
          refine ⟨10544912876072559344252303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28119767669526824918006141 10544912876072559344252303)
          ·
            refine ⟨15817369314108839016378455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544912876072559344252303 15817369314108839016378455)
            ·
              refine ⟨23726053971163258524567683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817369314108839016378455 23726053971163258524567683)
              ·
                refine ⟨35589080956744887786851525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23726053971163258524567683 35589080956744887786851525)
                ·
                  refine ⟨6672952679389666460034661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35589080956744887786851525 6672952679389666460034661)
                  ·
                    refine ⟨1251178627385562461256499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672952679389666460034661 1251178627385562461256499)
                    ·
                      rfl

theorem cell23_7309985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_7309985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7309985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7309985 prefixEnd_7309985 := by exact prefixLift 7309985
  have htrace : WordTrace (prefixWord ++ tailWord_7309985) baseStart_7309985 baseEnd_7309985 := by
    simpa [prefixWord, tailWord_7309985, baseEnd_7309985] using wordTrace_append hprefix tailTrace_7309985
  have hstable : (prefixWord ++ tailWord_7309985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7309985).length < 2 ^ (prefixWord ++ tailWord_7309985).sum := by decide
  have hdescent : baseEnd_7309985 < baseStart_7309985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7309985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310005 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7310005 : Nat := 118140960795 + 7310005 * 2 ^ 59
def prefixEnd_7310005 : Nat := 4983230072969 + 3 ^ 40 * 7310005 * 2
def baseEnd_7310005 : Nat := 3753546151769777305519405

theorem tailTrace_7310005 : CollatzResearch.WordTrace tailWord_7310005 prefixEnd_7310005 3753546151769777305519405 := by
  unfold tailWord_7310005
  simp only [CollatzResearch.WordTrace]
  refine ⟨266617785882107809304971469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177745190588071872869980979 266617785882107809304971469)
  ·
    refine ⟨99981669705790428489364301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266617785882107809304971469 99981669705790428489364301)
    ·
      refine ⟨37493126139671410683511613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99981669705790428489364301 37493126139671410683511613)
      ·
        refine ⟨14059922302376779006316855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37493126139671410683511613 14059922302376779006316855)
        ·
          refine ⟨21089883453565168509475283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059922302376779006316855 21089883453565168509475283)
          ·
            refine ⟨31634825180347752764212925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089883453565168509475283 31634825180347752764212925)
            ·
              refine ⟨11863059442630407286579847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31634825180347752764212925 11863059442630407286579847)
              ·
                refine ⟨17794589163945610929869771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11863059442630407286579847 17794589163945610929869771)
                ·
                  refine ⟨26691883745918416394804657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17794589163945610929869771 26691883745918416394804657)
                  ·
                    refine ⟨20018912809438812296103493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26691883745918416394804657 20018912809438812296103493)
                    ·
                      refine ⟨3753546151769777305519405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20018912809438812296103493 3753546151769777305519405)
                      ·
                        rfl

theorem cell23_7310005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7310005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310005 prefixEnd_7310005 := by exact prefixLift 7310005
  have htrace : WordTrace (prefixWord ++ tailWord_7310005) baseStart_7310005 baseEnd_7310005 := by
    simpa [prefixWord, tailWord_7310005, baseEnd_7310005] using wordTrace_append hprefix tailTrace_7310005
  have hstable : (prefixWord ++ tailWord_7310005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310005).length < 2 ^ (prefixWord ++ tailWord_7310005).sum := by decide
  have hdescent : baseEnd_7310005 < baseStart_7310005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310026 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_7310026 : Nat := 118140960795 + 7310026 * 2 ^ 59
def prefixEnd_7310026 : Nat := 4983230072969 + 3 ^ 40 * 7310026 * 2
def baseEnd_7310026 : Nat := 3753556934863521723356809

theorem tailTrace_7310026 : CollatzResearch.WordTrace tailWord_7310026 prefixEnd_7310026 3753556934863521723356809 := by
  unfold tailWord_7310026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66654637953757932472871483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177745701210021153260990621 66654637953757932472871483)
  ·
    refine ⟨99981956930636898709307225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66654637953757932472871483 99981956930636898709307225)
    ·
      refine ⟨74986467697977674031980419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99981956930636898709307225 74986467697977674031980419)
      ·
        refine ⟨112479701546966511047970629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74986467697977674031980419 112479701546966511047970629)
        ·
          refine ⟨21089944040056220821494493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112479701546966511047970629 21089944040056220821494493)
          ·
            refine ⟨7908729015021082808060435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21089944040056220821494493 7908729015021082808060435)
            ·
              refine ⟨11863093522531624212090653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908729015021082808060435 11863093522531624212090653)
              ·
                refine ⟨4448660070949359079533995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11863093522531624212090653 4448660070949359079533995)
                ·
                  refine ⟨6672990106424038619300993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448660070949359079533995 6672990106424038619300993)
                  ·
                    refine ⟨5004742579818028964475745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672990106424038619300993 5004742579818028964475745)
                    ·
                      refine ⟨3753556934863521723356809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004742579818028964475745 3753556934863521723356809)
                      ·
                        rfl

theorem cell23_7310026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_7310026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310026 prefixEnd_7310026 := by exact prefixLift 7310026
  have htrace : WordTrace (prefixWord ++ tailWord_7310026) baseStart_7310026 baseEnd_7310026 := by
    simpa [prefixWord, tailWord_7310026, baseEnd_7310026] using wordTrace_append hprefix tailTrace_7310026
  have hstable : (prefixWord ++ tailWord_7310026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310026).length < 2 ^ (prefixWord ++ tailWord_7310026).sum := by decide
  have hdescent : baseEnd_7310026 < baseStart_7310026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310031 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_7310031 : Nat := 118140960795 + 7310031 * 2 ^ 59
def prefixEnd_7310031 : Nat := 4983230072969 + 3 ^ 40 * 7310031 * 2
def baseEnd_7310031 : Nat := 3753559502266794203794285

theorem tailTrace_7310031 : CollatzResearch.WordTrace tailWord_7310031 prefixEnd_7310031 3753559502266794203794285 := by
  unfold tailWord_7310031
  simp only [CollatzResearch.WordTrace]
  refine ⟨266618734180013615745417947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177745822786675743830278631 266618734180013615745417947)
  ·
    refine ⟨399928101270020423618126921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266618734180013615745417947 399928101270020423618126921)
    ·
      refine ⟨299946075952515317713595191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399928101270020423618126921 299946075952515317713595191)
      ·
        refine ⟨449919113928772976570392787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299946075952515317713595191 449919113928772976570392787)
        ·
          refine ⟨674878670893159464855589181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449919113928772976570392787 674878670893159464855589181)
          ·
            refine ⟨253079501584934799320845943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674878670893159464855589181 253079501584934799320845943)
            ·
              refine ⟨379619252377402198981268915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253079501584934799320845943 379619252377402198981268915)
              ·
                refine ⟨569428878566103298471903373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379619252377402198981268915 569428878566103298471903373)
                ·
                  refine ⟨213535829462288736926963765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569428878566103298471903373 213535829462288736926963765)
                  ·
                    refine ⟨20018984012089569086902853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 213535829462288736926963765 20018984012089569086902853)
                    ·
                      refine ⟨3753559502266794203794285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20018984012089569086902853 3753559502266794203794285)
                      ·
                        rfl

theorem cell23_7310031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_7310031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310031 prefixEnd_7310031 := by exact prefixLift 7310031
  have htrace : WordTrace (prefixWord ++ tailWord_7310031) baseStart_7310031 baseEnd_7310031 := by
    simpa [prefixWord, tailWord_7310031, baseEnd_7310031] using wordTrace_append hprefix tailTrace_7310031
  have hstable : (prefixWord ++ tailWord_7310031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310031).length < 2 ^ (prefixWord ++ tailWord_7310031).sum := by decide
  have hdescent : baseEnd_7310031 < baseStart_7310031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310065 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_7310065 : Nat := 118140960795 + 7310065 * 2 ^ 59
def prefixEnd_7310065 : Nat := 4983230072969 + 3 ^ 40 * 7310065 * 2
def baseEnd_7310065 : Nat := 3753576960609047070769129

theorem tailTrace_7310065 : CollatzResearch.WordTrace tailWord_7310065 prefixEnd_7310065 3753576960609047070769129 := by
  unfold tailWord_7310065
  simp only [CollatzResearch.WordTrace]
  refine ⟨266619974261890439552155649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177746649507926959701437099 266619974261890439552155649)
  ·
    refine ⟨199964980696417829664116737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266619974261890439552155649 199964980696417829664116737)
    ·
      refine ⟨149973735522313372248087553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199964980696417829664116737 149973735522313372248087553)
      ·
        refine ⟨112480301641735029186065665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149973735522313372248087553 112480301641735029186065665)
        ·
          refine ⟨84360226231301271889549249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112480301641735029186065665 84360226231301271889549249)
          ·
            refine ⟨63270169673475953917161937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84360226231301271889549249 63270169673475953917161937)
            ·
              refine ⟨47452627255106965437871453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63270169673475953917161937 47452627255106965437871453)
              ·
                refine ⟨17794735220665112039201795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47452627255106965437871453 17794735220665112039201795)
                ·
                  refine ⟨26692102830997668058802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17794735220665112039201795 26692102830997668058802693)
                  ·
                    refine ⟨5004769280812062761025505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26692102830997668058802693 5004769280812062761025505)
                    ·
                      refine ⟨3753576960609047070769129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004769280812062761025505 3753576960609047070769129)
                      ·
                        rfl

theorem cell23_7310065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_7310065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310065 prefixEnd_7310065 := by exact prefixLift 7310065
  have htrace : WordTrace (prefixWord ++ tailWord_7310065) baseStart_7310065 baseEnd_7310065 := by
    simpa [prefixWord, tailWord_7310065, baseEnd_7310065] using wordTrace_append hprefix tailTrace_7310065
  have hstable : (prefixWord ++ tailWord_7310065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310065).length < 2 ^ (prefixWord ++ tailWord_7310065).sum := by decide
  have hdescent : baseEnd_7310065 < baseStart_7310065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310071 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 9]
def baseStart_7310071 : Nat := 118140960795 + 7310071 * 2 ^ 59
def prefixEnd_7310071 : Nat := 4983230072969 + 3 ^ 40 * 7310071 * 2
def baseEnd_7310071 : Nat := 417064449054774894143789

theorem tailTrace_7310071 : CollatzResearch.WordTrace tailWord_7310071 prefixEnd_7310071 417064449054774894143789 := by
  unfold tailWord_7310071
  simp only [CollatzResearch.WordTrace]
  refine ⟨266620193099868702576874067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177746795399912468384582711 266620193099868702576874067)
  ·
    refine ⟨399930289649803053865311101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266620193099868702576874067 399930289649803053865311101)
    ·
      refine ⟨149973858618676145199491663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399930289649803053865311101 149973858618676145199491663)
      ·
        refine ⟨224960787928014217799237495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149973858618676145199491663 224960787928014217799237495)
        ·
          refine ⟨337441181892021326698856243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224960787928014217799237495 337441181892021326698856243)
          ·
            refine ⟨506161772838031990048284365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337441181892021326698856243 506161772838031990048284365)
            ·
              refine ⟨189810664814261996268106637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506161772838031990048284365 189810664814261996268106637)
              ·
                refine ⟨71178999305348248600539989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189810664814261996268106637 71178999305348248600539989)
                ·
                  refine ⟨417064449054774894143789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71178999305348248600539989 417064449054774894143789)
                  ·
                    rfl

theorem cell23_7310071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 9].length) (baseStart_7310071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310071 prefixEnd_7310071 := by exact prefixLift 7310071
  have htrace : WordTrace (prefixWord ++ tailWord_7310071) baseStart_7310071 baseEnd_7310071 := by
    simpa [prefixWord, tailWord_7310071, baseEnd_7310071] using wordTrace_append hprefix tailTrace_7310071
  have hstable : (prefixWord ++ tailWord_7310071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310071).length < 2 ^ (prefixWord ++ tailWord_7310071).sum := by decide
  have hdescent : baseEnd_7310071 < baseStart_7310071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310082 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7310082 : Nat := 118140960795 + 7310082 * 2 ^ 59
def prefixEnd_7310082 : Nat := 4983230072969 + 3 ^ 40 * 7310082 * 2
def baseEnd_7310082 : Nat := 3753585689780173504256551

theorem tailTrace_7310082 : CollatzResearch.WordTrace tailWord_7310082 prefixEnd_7310082 3753585689780173504256551 := by
  unfold tailWord_7310082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66655148575707212863881125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177747062868552567637016333 66655148575707212863881125)
  ·
    refine ⟨12497840357945102411977711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66655148575707212863881125 12497840357945102411977711)
    ·
      refine ⟨18746760536917653617966567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497840357945102411977711 18746760536917653617966567)
      ·
        refine ⟨28120140805376480426949851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18746760536917653617966567 28120140805376480426949851)
        ·
          refine ⟨42180211208064720640424777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120140805376480426949851 42180211208064720640424777)
          ·
            refine ⟨31635158406048540480318583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42180211208064720640424777 31635158406048540480318583)
            ·
              refine ⟨47452737609072810720477875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31635158406048540480318583 47452737609072810720477875)
              ·
                refine ⟨71179106413609216080716813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47452737609072810720477875 71179106413609216080716813)
                ·
                  refine ⟨26692164905103456030268805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71179106413609216080716813 26692164905103456030268805)
                  ·
                    refine ⟨5004780919706898005675401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26692164905103456030268805 5004780919706898005675401)
                    ·
                      refine ⟨3753585689780173504256551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004780919706898005675401 3753585689780173504256551)
                      ·
                        rfl

theorem cell23_7310082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7310082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310082 prefixEnd_7310082 := by exact prefixLift 7310082
  have htrace : WordTrace (prefixWord ++ tailWord_7310082) baseStart_7310082 baseEnd_7310082 := by
    simpa [prefixWord, tailWord_7310082, baseEnd_7310082] using wordTrace_append hprefix tailTrace_7310082
  have hstable : (prefixWord ++ tailWord_7310082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310082).length < 2 ^ (prefixWord ++ tailWord_7310082).sum := by decide
  have hdescent : baseEnd_7310082 < baseStart_7310082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310122 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_7310122 : Nat := 118140960795 + 7310122 * 2 ^ 59
def prefixEnd_7310122 : Nat := 4983230072969 + 3 ^ 40 * 7310122 * 2
def baseEnd_7310122 : Nat := 417067358778483705306263

theorem tailTrace_7310122 : CollatzResearch.WordTrace tailWord_7310122 prefixEnd_7310122 417067358778483705306263 := by
  unfold tailWord_7310122
  simp only [CollatzResearch.WordTrace]
  refine ⟨66655513305670984571745155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177748035481789292191320413 66655513305670984571745155)
  ·
    refine ⟨99983269958506476857617733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66655513305670984571745155 99983269958506476857617733)
    ·
      refine ⟨18746863117219964410803325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99983269958506476857617733 18746863117219964410803325)
      ·
        refine ⟨7030073668957486654051247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18746863117219964410803325 7030073668957486654051247)
        ·
          refine ⟨10545110503436229981076871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030073668957486654051247 10545110503436229981076871)
          ·
            refine ⟨15817665755154344971615307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545110503436229981076871 15817665755154344971615307)
            ·
              refine ⟨23726498632731517457422961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817665755154344971615307 23726498632731517457422961)
              ·
                refine ⟨17794873974548638093067221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23726498632731517457422961 17794873974548638093067221)
                ·
                  refine ⟨417067358778483705306263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17794873974548638093067221 417067358778483705306263)
                  ·
                    rfl

theorem cell23_7310122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_7310122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310122 prefixEnd_7310122 := by exact prefixLift 7310122
  have htrace : WordTrace (prefixWord ++ tailWord_7310122) baseStart_7310122 baseEnd_7310122 := by
    simpa [prefixWord, tailWord_7310122, baseEnd_7310122] using wordTrace_append hprefix tailTrace_7310122
  have hstable : (prefixWord ++ tailWord_7310122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310122).length < 2 ^ (prefixWord ++ tailWord_7310122).sum := by decide
  have hdescent : baseEnd_7310122 < baseStart_7310122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310150 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7310150 : Nat := 118140960795 + 7310150 * 2 ^ 59
def prefixEnd_7310150 : Nat := 4983230072969 + 3 ^ 40 * 7310150 * 2
def baseEnd_7310150 : Nat := 3753620606464679238206239

theorem tailTrace_7310150 : CollatzResearch.WordTrace tailWord_7310150 prefixEnd_7310150 3753620606464679238206239 := by
  unfold tailWord_7310150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8331971077080703095906247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177748716311054999379333269 8331971077080703095906247)
  ·
    refine ⟨12497956615621054643859371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8331971077080703095906247 12497956615621054643859371)
    ·
      refine ⟨18746934923431581965789057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497956615621054643859371 18746934923431581965789057)
      ·
        refine ⟨14060201192573686474341793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18746934923431581965789057 14060201192573686474341793)
        ·
          refine ⟨10545150894430264855756345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14060201192573686474341793 10545150894430264855756345)
          ·
            refine ⟨7908863170822698641817259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10545150894430264855756345 7908863170822698641817259)
            ·
              refine ⟨11863294756234047962725889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908863170822698641817259 11863294756234047962725889)
              ·
                refine ⟨8897471067175535972044417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11863294756234047962725889 8897471067175535972044417)
                ·
                  refine ⟨6673103300381651979033313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8897471067175535972044417 6673103300381651979033313)
                  ·
                    refine ⟨5004827475286238984274985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673103300381651979033313 5004827475286238984274985)
                    ·
                      refine ⟨3753620606464679238206239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004827475286238984274985 3753620606464679238206239)
                      ·
                        rfl

theorem cell23_7310150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7310150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310150 prefixEnd_7310150 := by exact prefixLift 7310150
  have htrace : WordTrace (prefixWord ++ tailWord_7310150) baseStart_7310150 baseEnd_7310150 := by
    simpa [prefixWord, tailWord_7310150, baseEnd_7310150] using wordTrace_append hprefix tailTrace_7310150
  have hstable : (prefixWord ++ tailWord_7310150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310150).length < 2 ^ (prefixWord ++ tailWord_7310150).sum := by decide
  have hdescent : baseEnd_7310150 < baseStart_7310150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310158 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7310158 : Nat := 118140960795 + 7310158 * 2 ^ 59
def prefixEnd_7310158 : Nat := 4983230072969 + 3 ^ 40 * 7310158 * 2
def baseEnd_7310158 : Nat := 3753624714309915206906201

theorem tailTrace_7310158 : CollatzResearch.WordTrace tailWord_7310158 prefixEnd_7310158 3753624714309915206906201 := by
  unfold tailWord_7310158
  simp only [CollatzResearch.WordTrace]
  refine ⟨33327920781319189554411391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177748910833702344290194085 33327920781319189554411391)
  ·
    refine ⟨49991881171978784331617087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33327920781319189554411391 49991881171978784331617087)
    ·
      refine ⟨74987821757968176497425631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49991881171978784331617087 74987821757968176497425631)
      ·
        refine ⟨112481732636952264746138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74987821757968176497425631 112481732636952264746138447)
        ·
          refine ⟨168722598955428397119207671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112481732636952264746138447 168722598955428397119207671)
          ·
            refine ⟨253083898433142595678811507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168722598955428397119207671 253083898433142595678811507)
            ·
              refine ⟨379625847649713893518217261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253083898433142595678811507 379625847649713893518217261)
              ·
                refine ⟨142359692868642710069331473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379625847649713893518217261 142359692868642710069331473)
                ·
                  refine ⟨106769769651482032551998605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142359692868642710069331473 106769769651482032551998605)
                  ·
                    refine ⟨40038663619305762206999477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106769769651482032551998605 40038663619305762206999477)
                    ·
                      refine ⟨3753624714309915206906201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40038663619305762206999477 3753624714309915206906201)
                      ·
                        rfl

theorem cell23_7310158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7310158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310158 prefixEnd_7310158 := by exact prefixLift 7310158
  have htrace : WordTrace (prefixWord ++ tailWord_7310158) baseStart_7310158 baseEnd_7310158 := by
    simpa [prefixWord, tailWord_7310158, baseEnd_7310158] using wordTrace_append hprefix tailTrace_7310158
  have hstable : (prefixWord ++ tailWord_7310158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310158).length < 2 ^ (prefixWord ++ tailWord_7310158).sum := by decide
  have hdescent : baseEnd_7310158 < baseStart_7310158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310216 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 1, 4]
def baseStart_7310216 : Nat := 118140960795 + 7310216 * 2 ^ 59
def prefixEnd_7310216 : Nat := 4983230072969 + 3 ^ 40 * 7310216 * 2
def baseEnd_7310216 : Nat := 1251218165395958659993645

theorem tailTrace_7310216 : CollatzResearch.WordTrace tailWord_7310216 prefixEnd_7310216 1251218165395958659993645 := by
  unfold tailWord_7310216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133312740842171696170451251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177750321122895594893935001 133312740842171696170451251)
  ·
    refine ⟨199969111263257544255676877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133312740842171696170451251 199969111263257544255676877)
    ·
      refine ⟨74988416723721579095878829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199969111263257544255676877 74988416723721579095878829)
      ·
        refine ⟨28120656271395592160954561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74988416723721579095878829 28120656271395592160954561)
        ·
          refine ⟨21090492203546694120715921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28120656271395592160954561 21090492203546694120715921)
          ·
            refine ⟨15817869152660020590536941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21090492203546694120715921 15817869152660020590536941)
            ·
              refine ⟨5931700932247507721451353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15817869152660020590536941 5931700932247507721451353)
              ·
                refine ⟨4448775699185630791088515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931700932247507721451353 4448775699185630791088515)
                ·
                  refine ⟨6673163548778446186632773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448775699185630791088515 6673163548778446186632773)
                  ·
                    refine ⟨1251218165395958659993645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673163548778446186632773 1251218165395958659993645)
                    ·
                      rfl

theorem cell23_7310216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_7310216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310216 prefixEnd_7310216 := by exact prefixLift 7310216
  have htrace : WordTrace (prefixWord ++ tailWord_7310216) baseStart_7310216 baseEnd_7310216 := by
    simpa [prefixWord, tailWord_7310216, baseEnd_7310216] using wordTrace_append hprefix tailTrace_7310216
  have hstable : (prefixWord ++ tailWord_7310216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310216).length < 2 ^ (prefixWord ++ tailWord_7310216).sum := by decide
  have hdescent : baseEnd_7310216 < baseStart_7310216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310242 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7310242 : Nat := 118140960795 + 7310242 * 2 ^ 59
def prefixEnd_7310242 : Nat := 4983230072969 + 3 ^ 40 * 7310242 * 2
def baseEnd_7310242 : Nat := 1251222615561630959418605

theorem tailTrace_7310242 : CollatzResearch.WordTrace tailWord_7310242 prefixEnd_7310242 1251222615561630959418605 := by
  unfold tailWord_7310242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66656607495562299695337245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177750953321499465854232653 66656607495562299695337245)
  ·
    refine ⟨24996227810835862385751467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66656607495562299695337245 24996227810835862385751467)
    ·
      refine ⟨37494341716253793578627201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24996227810835862385751467 37494341716253793578627201)
      ·
        refine ⟨28120756287190345183970401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37494341716253793578627201 28120756287190345183970401)
        ·
          refine ⟨21090567215392758887977801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28120756287190345183970401 21090567215392758887977801)
          ·
            refine ⟨15817925411544569165983351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21090567215392758887977801 15817925411544569165983351)
            ·
              refine ⟨23726888117316853748975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817925411544569165983351 23726888117316853748975027)
              ·
                refine ⟨35590332175975280623462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23726888117316853748975027 35590332175975280623462541)
                ·
                  refine ⟨13346374565990730233798453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35590332175975280623462541 13346374565990730233798453)
                  ·
                    refine ⟨1251222615561630959418605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13346374565990730233798453 1251222615561630959418605)
                    ·
                      rfl

theorem cell23_7310242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7310242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310242 prefixEnd_7310242 := by exact prefixLift 7310242
  have htrace : WordTrace (prefixWord ++ tailWord_7310242) baseStart_7310242 baseEnd_7310242 := by
    simpa [prefixWord, tailWord_7310242, baseEnd_7310242] using wordTrace_append hprefix tailTrace_7310242
  have hstable : (prefixWord ++ tailWord_7310242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310242).length < 2 ^ (prefixWord ++ tailWord_7310242).sum := by decide
  have hdescent : baseEnd_7310242 < baseStart_7310242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310255 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 4, 4]
def baseStart_7310255 : Nat := 118140960795 + 7310255 * 2 ^ 59
def prefixEnd_7310255 : Nat := 4983230072969 + 3 ^ 40 * 7310255 * 2
def baseEnd_7310255 : Nat := 1251224840644467109131085

theorem tailTrace_7310255 : CollatzResearch.WordTrace tailWord_7310255 prefixEnd_7310255 1251224840644467109131085 := by
  unfold tailWord_7310255
  simp only [CollatzResearch.WordTrace]
  refine ⟨266626904131202102001572219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177751269420801401334381479 266626904131202102001572219)
  ·
    refine ⟨399940356196803153002358329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266626904131202102001572219 399940356196803153002358329)
    ·
      refine ⟨299955267147602364751768747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399940356196803153002358329 299955267147602364751768747)
      ·
        refine ⟨449932900721403547127653121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299955267147602364751768747 449932900721403547127653121)
        ·
          refine ⟨337449675541052660345739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449932900721403547127653121 337449675541052660345739841)
          ·
            refine ⟨253087256655789495259304881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337449675541052660345739841 253087256655789495259304881)
            ·
              refine ⟨189815442491842121444478661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253087256655789495259304881 189815442491842121444478661)
              ·
                refine ⟨35590395467220397770839749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189815442491842121444478661 35590395467220397770839749)
                ·
                  refine ⟨6673199150103824582032453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35590395467220397770839749 6673199150103824582032453)
                  ·
                    refine ⟨1251224840644467109131085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673199150103824582032453 1251224840644467109131085)
                    ·
                      rfl

theorem cell23_7310255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_7310255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310255 prefixEnd_7310255 := by exact prefixLift 7310255
  have htrace : WordTrace (prefixWord ++ tailWord_7310255) baseStart_7310255 baseEnd_7310255 := by
    simpa [prefixWord, tailWord_7310255, baseEnd_7310255] using wordTrace_append hprefix tailTrace_7310255
  have hstable : (prefixWord ++ tailWord_7310255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310255).length < 2 ^ (prefixWord ++ tailWord_7310255).sum := by decide
  have hdescent : baseEnd_7310255 < baseStart_7310255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310268 : List Nat := [2, 2, 2, 17]
def baseStart_7310268 : Nat := 118140960795 + 7310268 * 2 ^ 59
def prefixEnd_7310268 : Nat := 4983230072969 + 3 ^ 40 * 7310268 * 2
def baseEnd_7310268 : Nat := 1716360858336492810485

theorem tailTrace_7310268 : CollatzResearch.WordTrace tailWord_7310268 prefixEnd_7310268 1716360858336492810485 := by
  unfold tailWord_7310268
  simp only [CollatzResearch.WordTrace]
  refine ⟨133313689140077502610897729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177751585520103336814530305 133313689140077502610897729)
  ·
    refine ⟨99985266855058126958173297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133313689140077502610897729 99985266855058126958173297)
    ·
      refine ⟨74988950141293595218629973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99985266855058126958173297 74988950141293595218629973)
      ·
        refine ⟨1716360858336492810485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 74988950141293595218629973 1716360858336492810485)
        ·
          rfl

theorem cell23_7310268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 17].length) (baseStart_7310268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310268 prefixEnd_7310268 := by exact prefixLift 7310268
  have htrace : WordTrace (prefixWord ++ tailWord_7310268) baseStart_7310268 baseEnd_7310268 := by
    simpa [prefixWord, tailWord_7310268, baseEnd_7310268] using wordTrace_append hprefix tailTrace_7310268
  have hstable : (prefixWord ++ tailWord_7310268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310268).length < 2 ^ (prefixWord ++ tailWord_7310268).sum := by decide
  have hdescent : baseEnd_7310268 < baseStart_7310268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310272 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_7310272 : Nat := 118140960795 + 7310272 * 2 ^ 59
def prefixEnd_7310272 : Nat := 4983230072969 + 3 ^ 40 * 7310272 * 2
def baseEnd_7310272 : Nat := 1251227750368175920293559

theorem tailTrace_7310272 : CollatzResearch.WordTrace tailWord_7310272 prefixEnd_7310272 1251227750368175920293559 := by
  unfold tailWord_7310272
  simp only [CollatzResearch.WordTrace]
  refine ⟨133313762086070256952470535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177751682781427009269960713 133313762086070256952470535)
  ·
    refine ⟨199970643129105385428705803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133313762086070256952470535 199970643129105385428705803)
    ·
      refine ⟨299955964693658078143058705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199970643129105385428705803 299955964693658078143058705)
      ·
        refine ⟨224966973520243558607294029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299955964693658078143058705 224966973520243558607294029)
        ·
          refine ⟨84362615070091334477735261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224966973520243558607294029 84362615070091334477735261)
          ·
            refine ⟨31635980651284250429150723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84362615070091334477735261 31635980651284250429150723)
            ·
              refine ⟨47453970976926375643726085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31635980651284250429150723 47453970976926375643726085)
              ·
                refine ⟨8897619558173695433198641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47453970976926375643726085 8897619558173695433198641)
                ·
                  refine ⟨6673214668630271574898981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8897619558173695433198641 6673214668630271574898981)
                  ·
                    refine ⟨1251227750368175920293559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673214668630271574898981 1251227750368175920293559)
                    ·
                      rfl

theorem cell23_7310272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_7310272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310272 prefixEnd_7310272 := by exact prefixLift 7310272
  have htrace : WordTrace (prefixWord ++ tailWord_7310272) baseStart_7310272 baseEnd_7310272 := by
    simpa [prefixWord, tailWord_7310272, baseEnd_7310272] using wordTrace_append hprefix tailTrace_7310272
  have hstable : (prefixWord ++ tailWord_7310272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310272).length < 2 ^ (prefixWord ++ tailWord_7310272).sum := by decide
  have hdescent : baseEnd_7310272 < baseStart_7310272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310292 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7310292 : Nat := 118140960795 + 7310292 * 2 ^ 59
def prefixEnd_7310292 : Nat := 4983230072969 + 3 ^ 40 * 7310292 * 2
def baseEnd_7310292 : Nat := 3753693520717617682630585

theorem tailTrace_7310292 : CollatzResearch.WordTrace tailWord_7310292 prefixEnd_7310292 3753693520717617682630585 := by
  unfold tailWord_7310292
  simp only [CollatzResearch.WordTrace]
  refine ⟨133314126816034028660334565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177752169088045371547112753 133314126816034028660334565)
  ·
    refine ⟨24996398778006380373812731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133314126816034028660334565 24996398778006380373812731)
    ·
      refine ⟨37494598167009570560719097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24996398778006380373812731 37494598167009570560719097)
      ·
        refine ⟨28120948625257177920539323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37494598167009570560719097 28120948625257177920539323)
        ·
          refine ⟨42181422937885766880808985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120948625257177920539323 42181422937885766880808985)
          ·
            refine ⟨31636067203414325160606739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42181422937885766880808985 31636067203414325160606739)
            ·
              refine ⟨47454100805121487740910109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31636067203414325160606739 47454100805121487740910109)
              ·
                refine ⟨17795287801920557902841291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47454100805121487740910109 17795287801920557902841291)
                ·
                  refine ⟨26692931702880836854261937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17795287801920557902841291 26692931702880836854261937)
                  ·
                    refine ⟨20019698777160627640696453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26692931702880836854261937 20019698777160627640696453)
                    ·
                      refine ⟨3753693520717617682630585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20019698777160627640696453 3753693520717617682630585)
                      ·
                        rfl

theorem cell23_7310292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7310292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310292 prefixEnd_7310292 := by exact prefixLift 7310292
  have htrace : WordTrace (prefixWord ++ tailWord_7310292) baseStart_7310292 baseEnd_7310292 := by
    simpa [prefixWord, tailWord_7310292, baseEnd_7310292] using wordTrace_append hprefix tailTrace_7310292
  have hstable : (prefixWord ++ tailWord_7310292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310292).length < 2 ^ (prefixWord ++ tailWord_7310292).sum := by decide
  have hdescent : baseEnd_7310292 < baseStart_7310292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310312 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7310312 : Nat := 118140960795 + 7310312 * 2 ^ 59
def prefixEnd_7310312 : Nat := 4983230072969 + 3 ^ 40 * 7310312 * 2
def baseEnd_7310312 : Nat := 3753703790330707604380493

theorem tailTrace_7310312 : CollatzResearch.WordTrace tailWord_7310312 prefixEnd_7310312 3753703790330707604380493 := by
  unfold tailWord_7310312
  simp only [CollatzResearch.WordTrace]
  refine ⟨133314491545997800368198595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177752655394663733824264793 133314491545997800368198595)
  ·
    refine ⟨199971737318996700552297893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133314491545997800368198595 199971737318996700552297893)
    ·
      refine ⟨37494700747311881353555855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199971737318996700552297893 37494700747311881353555855)
      ·
        refine ⟨56242051120967822030333783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37494700747311881353555855 56242051120967822030333783)
        ·
          refine ⟨84363076681451733045500675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56242051120967822030333783 84363076681451733045500675)
          ·
            refine ⟨126544615022177599568251013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84363076681451733045500675 126544615022177599568251013)
            ·
              refine ⟨23727115316658299919047065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126544615022177599568251013 23727115316658299919047065)
              ·
                refine ⟨17795336487493724939285299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23727115316658299919047065 17795336487493724939285299)
                ·
                  refine ⟨26693004731240587408927949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17795336487493724939285299 26693004731240587408927949)
                  ·
                    refine ⟨10009876774215220278347981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26693004731240587408927949 10009876774215220278347981)
                    ·
                      refine ⟨3753703790330707604380493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10009876774215220278347981 3753703790330707604380493)
                      ·
                        rfl

theorem cell23_7310312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7310312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310312 prefixEnd_7310312 := by exact prefixLift 7310312
  have htrace : WordTrace (prefixWord ++ tailWord_7310312) baseStart_7310312 baseEnd_7310312 := by
    simpa [prefixWord, tailWord_7310312, baseEnd_7310312] using wordTrace_append hprefix tailTrace_7310312
  have hstable : (prefixWord ++ tailWord_7310312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310312).length < 2 ^ (prefixWord ++ tailWord_7310312).sum := by decide
  have hdescent : baseEnd_7310312 < baseStart_7310312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310355 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_7310355 : Nat := 118140960795 + 7310355 * 2 ^ 59
def prefixEnd_7310355 : Nat := 4983230072969 + 3 ^ 40 * 7310355 * 2
def baseEnd_7310355 : Nat := 3753725869998850936142795

theorem tailTrace_7310355 : CollatzResearch.WordTrace tailWord_7310355 prefixEnd_7310355 3753725869998850936142795 := by
  unfold tailWord_7310355
  simp only [CollatzResearch.WordTrace]
  refine ⟨266630551430839819080212519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177753700953893212720141679 266630551430839819080212519)
  ·
    refine ⟨399945827146259728620318779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266630551430839819080212519 399945827146259728620318779)
    ·
      refine ⟨599918740719389592930478169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399945827146259728620318779 599918740719389592930478169)
      ·
        refine ⟨449939055539542194697858627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599918740719389592930478169 449939055539542194697858627)
        ·
          refine ⟨674908583309313292046787941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449939055539542194697858627 674908583309313292046787941)
          ·
            refine ⟨126545359370496242258772739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 674908583309313292046787941 126545359370496242258772739)
            ·
              refine ⟨189818039055744363388159109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126545359370496242258772739 189818039055744363388159109)
              ·
                refine ⟨35590882322952068135279833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189818039055744363388159109 35590882322952068135279833)
                ·
                  refine ⟨26693161742214051101459875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35590882322952068135279833 26693161742214051101459875)
                  ·
                    refine ⟨40039742613321076652189813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26693161742214051101459875 40039742613321076652189813)
                    ·
                      refine ⟨3753725869998850936142795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40039742613321076652189813 3753725869998850936142795)
                      ·
                        rfl

theorem cell23_7310355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_7310355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310355 prefixEnd_7310355 := by exact prefixLift 7310355
  have htrace : WordTrace (prefixWord ++ tailWord_7310355) baseStart_7310355 baseEnd_7310355 := by
    simpa [prefixWord, tailWord_7310355, baseEnd_7310355] using wordTrace_append hprefix tailTrace_7310355
  have hstable : (prefixWord ++ tailWord_7310355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310355).length < 2 ^ (prefixWord ++ tailWord_7310355).sum := by decide
  have hdescent : baseEnd_7310355 < baseStart_7310355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310372 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7310372 : Nat := 118140960795 + 7310372 * 2 ^ 59
def prefixEnd_7310372 : Nat := 4983230072969 + 3 ^ 40 * 7310372 * 2
def baseEnd_7310372 : Nat := 3753734599169977369630217

theorem tailTrace_7310372 : CollatzResearch.WordTrace tailWord_7310372 prefixEnd_7310372 3753734599169977369630217 := by
  unfold tailWord_7310372
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315585735889115491790685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177754114314518820655720913 133315585735889115491790685)
  ·
    refine ⟨49993344650958418309421507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133315585735889115491790685 49993344650958418309421507)
    ·
      refine ⟨74990016976437627464132261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49993344650958418309421507 74990016976437627464132261)
      ·
        refine ⟨14060628183082055149524799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74990016976437627464132261 14060628183082055149524799)
        ·
          refine ⟨21090942274623082724287199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14060628183082055149524799 21090942274623082724287199)
          ·
            refine ⟨31636413411934624086430799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21090942274623082724287199 31636413411934624086430799)
            ·
              refine ⟨47454620117901936129646199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31636413411934624086430799 47454620117901936129646199)
              ·
                refine ⟨71181930176852904194469299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47454620117901936129646199 71181930176852904194469299)
                ·
                  refine ⟨106772895265279356291703949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71181930176852904194469299 106772895265279356291703949)
                  ·
                    refine ⟨40039835724479758609388981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106772895265279356291703949 40039835724479758609388981)
                    ·
                      refine ⟨3753734599169977369630217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40039835724479758609388981 3753734599169977369630217)
                      ·
                        rfl

theorem cell23_7310372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7310372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310372 prefixEnd_7310372 := by exact prefixLift 7310372
  have htrace : WordTrace (prefixWord ++ tailWord_7310372) baseStart_7310372 baseEnd_7310372 := by
    simpa [prefixWord, tailWord_7310372, baseEnd_7310372] using wordTrace_append hprefix tailTrace_7310372
  have hstable : (prefixWord ++ tailWord_7310372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310372).length < 2 ^ (prefixWord ++ tailWord_7310372).sum := by decide
  have hdescent : baseEnd_7310372 < baseStart_7310372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310385 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7310385 : Nat := 118140960795 + 7310385 * 2 ^ 59
def prefixEnd_7310385 : Nat := 4983230072969 + 3 ^ 40 * 7310385 * 2
def baseEnd_7310385 : Nat := 3753741274418485818767657

theorem tailTrace_7310385 : CollatzResearch.WordTrace tailWord_7310385 prefixEnd_7310385 3753741274418485818767657 := by
  unfold tailWord_7310385
  simp only [CollatzResearch.WordTrace]
  refine ⟨266631645620731134203804609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177754430413820756135869739 266631645620731134203804609)
  ·
    refine ⟨199973734215548350652853457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266631645620731134203804609 199973734215548350652853457)
    ·
      refine ⟨149980300661661262989640093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199973734215548350652853457 149980300661661262989640093)
      ·
        refine ⟨56242612748122973621115035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149980300661661262989640093 56242612748122973621115035)
        ·
          refine ⟨84363919122184460431672553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56242612748122973621115035 84363919122184460431672553)
          ·
            refine ⟨63272939341638345323754415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84363919122184460431672553 63272939341638345323754415)
            ·
              refine ⟨94909409012457517985631623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63272939341638345323754415 94909409012457517985631623)
              ·
                refine ⟨142364113518686276978447435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94909409012457517985631623 142364113518686276978447435)
                ·
                  refine ⟨213546170278029415467671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142364113518686276978447435 213546170278029415467671153)
                  ·
                    refine ⟨160159627708522061600753365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213546170278029415467671153 160159627708522061600753365)
                    ·
                      refine ⟨3753741274418485818767657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160159627708522061600753365 3753741274418485818767657)
                      ·
                        rfl

theorem cell23_7310385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7310385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310385 prefixEnd_7310385 := by exact prefixLift 7310385
  have htrace : WordTrace (prefixWord ++ tailWord_7310385) baseStart_7310385 baseEnd_7310385 := by
    simpa [prefixWord, tailWord_7310385, baseEnd_7310385] using wordTrace_append hprefix tailTrace_7310385
  have hstable : (prefixWord ++ tailWord_7310385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310385).length < 2 ^ (prefixWord ++ tailWord_7310385).sum := by decide
  have hdescent : baseEnd_7310385 < baseStart_7310385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310386 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_7310386 : Nat := 118140960795 + 7310386 * 2 ^ 59
def prefixEnd_7310386 : Nat := 4983230072969 + 3 ^ 40 * 7310386 * 2
def baseEnd_7310386 : Nat := 3753741787899140314855153

theorem tailTrace_7310386 : CollatzResearch.WordTrace tailWord_7310386 prefixEnd_7310386 3753741787899140314855153 := by
  unfold tailWord_7310386
  simp only [CollatzResearch.WordTrace]
  refine ⟨66657920523431877843647753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177754454729151674249727341 66657920523431877843647753)
  ·
    refine ⟨49993440392573908382735815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66657920523431877843647753 49993440392573908382735815)
    ·
      refine ⟨74990160588860862574103723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49993440392573908382735815 74990160588860862574103723)
      ·
        refine ⟨112485240883291293861155585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74990160588860862574103723 112485240883291293861155585)
        ·
          refine ⟨84363930662468470395866689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112485240883291293861155585 84363930662468470395866689)
          ·
            refine ⟨63272947996851352796900017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84363930662468470395866689 63272947996851352796900017)
            ·
              refine ⟨47454710997638514597675013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63272947996851352796900017 47454710997638514597675013)
              ·
                refine ⟨8897758312057221487064065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47454710997638514597675013 8897758312057221487064065)
                ·
                  refine ⟨6673318734042916115298049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8897758312057221487064065 6673318734042916115298049)
                  ·
                    refine ⟨5004989050532187086473537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673318734042916115298049 5004989050532187086473537)
                    ·
                      refine ⟨3753741787899140314855153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5004989050532187086473537 3753741787899140314855153)
                      ·
                        rfl

theorem cell23_7310386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_7310386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310386 prefixEnd_7310386 := by exact prefixLift 7310386
  have htrace : WordTrace (prefixWord ++ tailWord_7310386) baseStart_7310386 baseEnd_7310386 := by
    simpa [prefixWord, tailWord_7310386, baseEnd_7310386] using wordTrace_append hprefix tailTrace_7310386
  have hstable : (prefixWord ++ tailWord_7310386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310386).length < 2 ^ (prefixWord ++ tailWord_7310386).sum := by decide
  have hdescent : baseEnd_7310386 < baseStart_7310386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310392 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 7]
def baseStart_7310392 : Nat := 118140960795 + 7310392 * 2 ^ 59
def prefixEnd_7310392 : Nat := 4983230072969 + 3 ^ 40 * 7310392 * 2
def baseEnd_7310392 : Nat := 417082763198118587931125

theorem tailTrace_7310392 : CollatzResearch.WordTrace tailWord_7310392 prefixEnd_7310392 417082763198118587931125 := by
  unfold tailWord_7310392
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315950465852887199654715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177754600621137182932872953 133315950465852887199654715)
  ·
    refine ⟨199973925698779330799482073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133315950465852887199654715 199973925698779330799482073)
    ·
      refine ⟨149980444274084498099611555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199973925698779330799482073 149980444274084498099611555)
      ·
        refine ⟨224970666411126747149417333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149980444274084498099611555 224970666411126747149417333)
        ·
          refine ⟨21090999976043132545257875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224970666411126747149417333 21090999976043132545257875)
          ·
            refine ⟨31636499964064698817886813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21090999976043132545257875 31636499964064698817886813)
            ·
              refine ⟨11863687486524262056707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31636499964064698817886813 11863687486524262056707555)
              ·
                refine ⟨17795531229786393085061333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11863687486524262056707555 17795531229786393085061333)
                ·
                  refine ⟨417082763198118587931125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17795531229786393085061333 417082763198118587931125)
                  ·
                    rfl

theorem cell23_7310392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_7310392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310392 prefixEnd_7310392 := by exact prefixLift 7310392
  have htrace : WordTrace (prefixWord ++ tailWord_7310392) baseStart_7310392 baseEnd_7310392 := by
    simpa [prefixWord, tailWord_7310392, baseEnd_7310392] using wordTrace_append hprefix tailTrace_7310392
  have hstable : (prefixWord ++ tailWord_7310392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310392).length < 2 ^ (prefixWord ++ tailWord_7310392).sum := by decide
  have hdescent : baseEnd_7310392 < baseStart_7310392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310405 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_7310405 : Nat := 118140960795 + 7310405 * 2 ^ 59
def prefixEnd_7310405 : Nat := 4983230072969 + 3 ^ 40 * 7310405 * 2
def baseEnd_7310405 : Nat := 1251250514677191913505855

theorem tailTrace_7310405 : CollatzResearch.WordTrace tailWord_7310405 prefixEnd_7310405 1251250514677191913505855 := by
  unfold tailWord_7310405
  simp only [CollatzResearch.WordTrace]
  refine ⟨266632375080658677619532669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177754916720439118413021779 266632375080658677619532669)
  ·
    refine ⟨99987140655247004107324751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266632375080658677619532669 99987140655247004107324751)
    ·
      refine ⟨149980710982870506160987127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99987140655247004107324751 149980710982870506160987127)
      ·
        refine ⟨224971066474305759241480691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149980710982870506160987127 224971066474305759241480691)
        ·
          refine ⟨337456599711458638862221037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224971066474305759241480691 337456599711458638862221037)
          ·
            refine ⟨126546224891796989573332889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337456599711458638862221037 126546224891796989573332889)
            ·
              refine ⟨94909668668847742179999667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126546224891796989573332889 94909668668847742179999667)
              ·
                refine ⟨142364503003271613269999501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94909668668847742179999667 142364503003271613269999501)
                ·
                  refine ⟨53386688626226854976249813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142364503003271613269999501 53386688626226854976249813)
                  ·
                    refine ⟨1251250514677191913505855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53386688626226854976249813 1251250514677191913505855)
                    ·
                      rfl

theorem cell23_7310405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_7310405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310405 prefixEnd_7310405 := by exact prefixLift 7310405
  have htrace : WordTrace (prefixWord ++ tailWord_7310405) baseStart_7310405 baseEnd_7310405 := by
    simpa [prefixWord, tailWord_7310405, baseEnd_7310405] using wordTrace_append hprefix tailTrace_7310405
  have hstable : (prefixWord ++ tailWord_7310405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310405).length < 2 ^ (prefixWord ++ tailWord_7310405).sum := by decide
  have hdescent : baseEnd_7310405 < baseStart_7310405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310415 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_7310415 : Nat := 118140960795 + 7310415 * 2 ^ 59
def prefixEnd_7310415 : Nat := 4983230072969 + 3 ^ 40 * 7310415 * 2
def baseEnd_7310415 : Nat := 3753756678838120701392519

theorem tailTrace_7310415 : CollatzResearch.WordTrace tailWord_7310415 prefixEnd_7310415 3753756678838120701392519 := by
  unfold tailWord_7310415
  simp only [CollatzResearch.WordTrace]
  refine ⟨266632739810622449327396699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177755159873748299551597799 266632739810622449327396699)
  ·
    refine ⟨399949109715933673991095049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266632739810622449327396699 399949109715933673991095049)
    ·
      refine ⟨299961832286950255493321287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399949109715933673991095049 299961832286950255493321287)
      ·
        refine ⟨449942748430425383239981931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299961832286950255493321287 449942748430425383239981931)
        ·
          refine ⟨674914122645638074859972897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449942748430425383239981931 674914122645638074859972897)
          ·
            refine ⟨506185591984228556144979673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674914122645638074859972897 506185591984228556144979673)
            ·
              refine ⟨379639193988171417108734755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506185591984228556144979673 379639193988171417108734755)
              ·
                refine ⟨569458790982257125663102133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379639193988171417108734755 569458790982257125663102133)
                ·
                  refine ⟨53386761654586605530915825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569458790982257125663102133 53386761654586605530915825)
                  ·
                    refine ⟨40040071240939954148186869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53386761654586605530915825 40040071240939954148186869)
                    ·
                      refine ⟨3753756678838120701392519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40040071240939954148186869 3753756678838120701392519)
                      ·
                        rfl

theorem cell23_7310415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_7310415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310415 prefixEnd_7310415 := by exact prefixLift 7310415
  have htrace : WordTrace (prefixWord ++ tailWord_7310415) baseStart_7310415 baseEnd_7310415 := by
    simpa [prefixWord, tailWord_7310415, baseEnd_7310415] using wordTrace_append hprefix tailTrace_7310415
  have hstable : (prefixWord ++ tailWord_7310415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310415).length < 2 ^ (prefixWord ++ tailWord_7310415).sum := by decide
  have hdescent : baseEnd_7310415 < baseStart_7310415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310503 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 1, 4]
def baseStart_7310503 : Nat := 118140960795 + 7310503 * 2 ^ 59
def prefixEnd_7310503 : Nat := 4983230072969 + 3 ^ 40 * 7310503 * 2
def baseEnd_7310503 : Nat := 1251267288378572119030705

theorem tailTrace_7310503 : CollatzResearch.WordTrace tailWord_7310503 prefixEnd_7310503 1251267288378572119030705 := by
  unfold tailWord_7310503
  simp only [CollatzResearch.WordTrace]
  refine ⟨266635949434303640356600163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177757299622869093571066775 266635949434303640356600163)
  ·
    refine ⟨399953924151455460534900245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266635949434303640356600163 399953924151455460534900245)
    ·
      refine ⟨18747840194599474712573449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 399953924151455460534900245 18747840194599474712573449)
      ·
        refine ⟨14060880145949606034430087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18747840194599474712573449 14060880145949606034430087)
        ·
          refine ⟨21091320218924409051645131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14060880145949606034430087 21091320218924409051645131)
          ·
            refine ⟨31636980328386613577467697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21091320218924409051645131 31636980328386613577467697)
            ·
              refine ⟨23727735246289960183100773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31636980328386613577467697 23727735246289960183100773)
              ·
                refine ⟨4448950358679367534331395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23727735246289960183100773 4448950358679367534331395)
                ·
                  refine ⟨6673425538019051301497093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448950358679367534331395 6673425538019051301497093)
                  ·
                    refine ⟨1251267288378572119030705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673425538019051301497093 1251267288378572119030705)
                    ·
                      rfl

theorem cell23_7310503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_7310503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310503 prefixEnd_7310503 := by exact prefixLift 7310503
  have htrace : WordTrace (prefixWord ++ tailWord_7310503) baseStart_7310503 baseEnd_7310503 := by
    simpa [prefixWord, tailWord_7310503, baseEnd_7310503] using wordTrace_append hprefix tailTrace_7310503
  have hstable : (prefixWord ++ tailWord_7310503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310503).length < 2 ^ (prefixWord ++ tailWord_7310503).sum := by decide
  have hdescent : baseEnd_7310503 < baseStart_7310503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310519 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_7310519 : Nat := 118140960795 + 7310519 * 2 ^ 59
def prefixEnd_7310519 : Nat := 4983230072969 + 3 ^ 40 * 7310519 * 2
def baseEnd_7310519 : Nat := 3753810080826188294492041

theorem tailTrace_7310519 : CollatzResearch.WordTrace tailWord_7310519 prefixEnd_7310519 3753810080826188294492041 := by
  unfold tailWord_7310519
  simp only [CollatzResearch.WordTrace]
  refine ⟨266636533002245675089182611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177757688668163783392788407 266636533002245675089182611)
  ·
    refine ⟨399954799503368512633773917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266636533002245675089182611 399954799503368512633773917)
    ·
      refine ⟨149983049813763192237665219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399954799503368512633773917 149983049813763192237665219)
      ·
        refine ⟨224974574720644788356497829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149983049813763192237665219 224974574720644788356497829)
        ·
          refine ⟨42182732760120897816843343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224974574720644788356497829 42182732760120897816843343)
          ·
            refine ⟨63274099140181346725265015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42182732760120897816843343 63274099140181346725265015)
            ·
              refine ⟨94911148710272020087897523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63274099140181346725265015 94911148710272020087897523)
              ·
                refine ⟨142366723065408030131846285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94911148710272020087897523 142366723065408030131846285)
                ·
                  refine ⟨53387521149528011299442357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142366723065408030131846285 53387521149528011299442357)
                  ·
                    refine ⟨5005080107768251059322721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53387521149528011299442357 5005080107768251059322721)
                    ·
                      refine ⟨3753810080826188294492041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005080107768251059322721 3753810080826188294492041)
                      ·
                        rfl

theorem cell23_7310519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_7310519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310519 prefixEnd_7310519 := by exact prefixLift 7310519
  have htrace : WordTrace (prefixWord ++ tailWord_7310519) baseStart_7310519 baseEnd_7310519 := by
    simpa [prefixWord, tailWord_7310519, baseEnd_7310519] using wordTrace_append hprefix tailTrace_7310519
  have hstable : (prefixWord ++ tailWord_7310519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310519).length < 2 ^ (prefixWord ++ tailWord_7310519).sum := by decide
  have hdescent : baseEnd_7310519 < baseStart_7310519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310559 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 4, 4]
def baseStart_7310559 : Nat := 118140960795 + 7310559 * 2 ^ 59
def prefixEnd_7310559 : Nat := 4983230072969 + 3 ^ 40 * 7310559 * 2
def baseEnd_7310559 : Nat := 1251276873350789379330619

theorem tailTrace_7310559 : CollatzResearch.WordTrace tailWord_7310559 prefixEnd_7310559 1251276873350789379330619 := by
  unfold tailWord_7310559
  simp only [CollatzResearch.WordTrace]
  refine ⟨266637991922100761920638731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177758661281400507947092487 266637991922100761920638731)
  ·
    refine ⟨399956987883151142880958097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266637991922100761920638731 399956987883151142880958097)
    ·
      refine ⟨299967740912363357160718573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399956987883151142880958097 299967740912363357160718573)
      ·
        refine ⟨112487902842136258935269465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299967740912363357160718573 112487902842136258935269465)
        ·
          refine ⟨84365927131602194201452099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112487902842136258935269465 84365927131602194201452099)
          ·
            refine ⟨126548890697403291302178149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84365927131602194201452099 126548890697403291302178149)
            ·
              refine ⟨23727917005763117119158403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126548890697403291302178149 23727917005763117119158403)
              ·
                refine ⟨35591875508644675678737605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23727917005763117119158403 35591875508644675678737605)
                ·
                  refine ⟨6673476657870876689763301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35591875508644675678737605 6673476657870876689763301)
                  ·
                    refine ⟨1251276873350789379330619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673476657870876689763301 1251276873350789379330619)
                    ·
                      rfl

theorem cell23_7310559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_7310559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310559 prefixEnd_7310559 := by exact prefixLift 7310559
  have htrace : WordTrace (prefixWord ++ tailWord_7310559) baseStart_7310559 baseEnd_7310559 := by
    simpa [prefixWord, tailWord_7310559, baseEnd_7310559] using wordTrace_append hprefix tailTrace_7310559
  have hstable : (prefixWord ++ tailWord_7310559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310559).length < 2 ^ (prefixWord ++ tailWord_7310559).sum := by decide
  have hdescent : baseEnd_7310559 < baseStart_7310559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310560 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 1, 1, 3]
def baseStart_7310560 : Nat := 118140960795 + 7310560 * 2 ^ 59
def prefixEnd_7310560 : Nat := 4983230072969 + 3 ^ 40 * 7310560 * 2
def baseEnd_7310560 : Nat := 3753831133533022634079353

theorem tailTrace_7310560 : CollatzResearch.WordTrace tailWord_7310560 prefixEnd_7310560 3753831133533022634079353 := by
  unfold tailWord_7310560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319014197548569545712567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177758685596731426060950089 133319014197548569545712567)
  ·
    refine ⟨199978521296322854318568851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133319014197548569545712567 199978521296322854318568851)
    ·
      refine ⟨299967781944484281477853277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199978521296322854318568851 299967781944484281477853277)
      ·
        refine ⟨112487918229181605554194979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299967781944484281477853277 112487918229181605554194979)
        ·
          refine ⟨168731877343772408331292469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112487918229181605554194979 168731877343772408331292469)
          ·
            refine ⟨15818613500978663281058669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168731877343772408331292469 15818613500978663281058669)
            ·
              refine ⟨5931980062866998730397001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15818613500978663281058669 5931980062866998730397001)
              ·
                refine ⟨4448985047150249047797751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931980062866998730397001 4448985047150249047797751)
                ·
                  refine ⟨6673477570725373571696627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448985047150249047797751 6673477570725373571696627)
                  ·
                    refine ⟨10010216356088060357544941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6673477570725373571696627 10010216356088060357544941)
                    ·
                      refine ⟨3753831133533022634079353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10010216356088060357544941 3753831133533022634079353)
                      ·
                        rfl

theorem cell23_7310560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_7310560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310560 prefixEnd_7310560 := by exact prefixLift 7310560
  have htrace : WordTrace (prefixWord ++ tailWord_7310560) baseStart_7310560 baseEnd_7310560 := by
    simpa [prefixWord, tailWord_7310560, baseEnd_7310560] using wordTrace_append hprefix tailTrace_7310560
  have hstable : (prefixWord ++ tailWord_7310560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310560).length < 2 ^ (prefixWord ++ tailWord_7310560).sum := by decide
  have hdescent : baseEnd_7310560 < baseStart_7310560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310572 : List Nat := [2, 2, 1, 1, 2, 4, 1, 10]
def baseStart_7310572 : Nat := 118140960795 + 7310572 * 2 ^ 59
def prefixEnd_7310572 : Nat := 4983230072969 + 3 ^ 40 * 7310572 * 2
def baseEnd_7310572 : Nat := 139031010937069503227011

theorem tailTrace_7310572 : CollatzResearch.WordTrace tailWord_7310572 prefixEnd_7310572 139031010937069503227011 := by
  unfold tailWord_7310572
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319233035526832570430985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177758977380702443427241313 133319233035526832570430985)
  ·
    refine ⟨99989424776645124427823239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133319233035526832570430985 99989424776645124427823239)
    ·
      refine ⟨149984137164967686641734859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99989424776645124427823239 149984137164967686641734859)
      ·
        refine ⟨224976205747451529962602289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149984137164967686641734859 224976205747451529962602289)
        ·
          refine ⟨168732154310588647471951717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224976205747451529962602289 168732154310588647471951717)
          ·
            refine ⟨31637278933235371400990947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168732154310588647471951717 31637278933235371400990947)
            ·
              refine ⟨47455918399853057101486421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31637278933235371400990947 47455918399853057101486421)
              ·
                refine ⟨139031010937069503227011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47455918399853057101486421 139031010937069503227011)
                ·
                  rfl

theorem cell23_7310572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 10].length) (baseStart_7310572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310572 prefixEnd_7310572 := by exact prefixLift 7310572
  have htrace : WordTrace (prefixWord ++ tailWord_7310572) baseStart_7310572 baseEnd_7310572 := by
    simpa [prefixWord, tailWord_7310572, baseEnd_7310572] using wordTrace_append hprefix tailTrace_7310572
  have hstable : (prefixWord ++ tailWord_7310572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310572).length < 2 ^ (prefixWord ++ tailWord_7310572).sum := by decide
  have hdescent : baseEnd_7310572 < baseStart_7310572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310580 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7310580 : Nat := 118140960795 + 7310580 * 2 ^ 59
def prefixEnd_7310580 : Nat := 4983230072969 + 3 ^ 40 * 7310580 * 2
def baseEnd_7310580 : Nat := 1251280467715370851943087

theorem tailTrace_7310580 : CollatzResearch.WordTrace tailWord_7310580 prefixEnd_7310580 1251280467715370851943087 := by
  unfold tailWord_7310580
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319378927512341253576597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177759171903349788338102129 133319378927512341253576597)
  ·
    refine ⟨6249345887227140996261403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133319378927512341253576597 6249345887227140996261403)
    ·
      refine ⟨9374018830840711494392105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249345887227140996261403 9374018830840711494392105)
      ·
        refine ⟨7030514123130533620794079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9374018830840711494392105 7030514123130533620794079)
        ·
          refine ⟨10545771184695800431191119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030514123130533620794079 10545771184695800431191119)
          ·
            refine ⟨15818656777043700646786679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545771184695800431191119 15818656777043700646786679)
            ·
              refine ⟨23727985165565550970180019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15818656777043700646786679 23727985165565550970180019)
              ·
                refine ⟨35591977748348326455270029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23727985165565550970180019 35591977748348326455270029)
                ·
                  refine ⟨13346991655630622420726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35591977748348326455270029 13346991655630622420726261)
                  ·
                    refine ⟨1251280467715370851943087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13346991655630622420726261 1251280467715370851943087)
                    ·
                      rfl

theorem cell23_7310580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7310580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310580 prefixEnd_7310580 := by exact prefixLift 7310580
  have htrace : WordTrace (prefixWord ++ tailWord_7310580) baseStart_7310580 baseEnd_7310580 := by
    simpa [prefixWord, tailWord_7310580, baseEnd_7310580] using wordTrace_append hprefix tailTrace_7310580
  have hstable : (prefixWord ++ tailWord_7310580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310580).length < 2 ^ (prefixWord ++ tailWord_7310580).sum := by decide
  have hdescent : baseEnd_7310580 < baseStart_7310580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310596 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7310596 : Nat := 118140960795 + 7310596 * 2 ^ 59
def prefixEnd_7310596 : Nat := 4983230072969 + 3 ^ 40 * 7310596 * 2
def baseEnd_7310596 : Nat := 3753849618836584493229187

theorem tailTrace_7310596 : CollatzResearch.WordTrace tailWord_7310596 prefixEnd_7310596 3753849618836584493229187 := by
  unfold tailWord_7310596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319670711483358619867821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177759560948644478159823761 133319670711483358619867821)
  ·
    refine ⟨49994876516806259482450433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133319670711483358619867821 49994876516806259482450433)
    ·
      refine ⟨37496157387604694611837825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49994876516806259482450433 37496157387604694611837825)
      ·
        refine ⟨28122118040703520958878369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37496157387604694611837825 28122118040703520958878369)
        ·
          refine ⟨21091588530527640719158777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28122118040703520958878369 21091588530527640719158777)
          ·
            refine ⟨15818691397895730539369083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21091588530527640719158777 15818691397895730539369083)
            ·
              refine ⟨23728037096843595809053625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15818691397895730539369083 23728037096843595809053625)
              ·
                refine ⟨17796027822632696856790219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23728037096843595809053625 17796027822632696856790219)
                ·
                  refine ⟨26694041733949045285185329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796027822632696856790219 26694041733949045285185329)
                  ·
                    refine ⟨20020531300461783963888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26694041733949045285185329 20020531300461783963888997)
                    ·
                      refine ⟨3753849618836584493229187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20020531300461783963888997 3753849618836584493229187)
                      ·
                        rfl

theorem cell23_7310596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7310596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310596 prefixEnd_7310596 := by exact prefixLift 7310596
  have htrace : WordTrace (prefixWord ++ tailWord_7310596) baseStart_7310596 baseEnd_7310596 := by
    simpa [prefixWord, tailWord_7310596, baseEnd_7310596] using wordTrace_append hprefix tailTrace_7310596
  have hstable : (prefixWord ++ tailWord_7310596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310596).length < 2 ^ (prefixWord ++ tailWord_7310596).sum := by decide
  have hdescent : baseEnd_7310596 < baseStart_7310596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310603 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 1, 2, 3]
def baseStart_7310603 : Nat := 118140960795 + 7310603 * 2 ^ 59
def prefixEnd_7310603 : Nat := 4983230072969 + 3 ^ 40 * 7310603 * 2
def baseEnd_7310603 : Nat := 3753853213201165965841655

theorem tailTrace_7310603 : CollatzResearch.WordTrace tailWord_7310603 prefixEnd_7310603 3753853213201165965841655 := by
  unfold tailWord_7310603
  simp only [CollatzResearch.WordTrace]
  refine ⟨266639596733941357435240463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177759731155960904956826975 266639596733941357435240463)
  ·
    refine ⟨399959395100912036152860695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266639596733941357435240463 399959395100912036152860695)
    ·
      refine ⟨599939092651368054229291043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399959395100912036152860695 599939092651368054229291043)
      ·
        refine ⟨899908638977052081343936565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599939092651368054229291043 899908638977052081343936565)
        ·
          refine ⟨84366434904098632625994053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 899908638977052081343936565 84366434904098632625994053)
          ·
            refine ⟨15818706544518493617373885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84366434904098632625994053 15818706544518493617373885)
            ·
              refine ⟨5932014954194435106515207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15818706544518493617373885 5932014954194435106515207)
              ·
                refine ⟨8898022431291652659772811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932014954194435106515207 8898022431291652659772811)
                ·
                  refine ⟨13347033646937478989659217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898022431291652659772811 13347033646937478989659217)
                  ·
                    refine ⟨10010275235203109242244413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347033646937478989659217 10010275235203109242244413)
                    ·
                      refine ⟨3753853213201165965841655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10010275235203109242244413 3753853213201165965841655)
                      ·
                        rfl

theorem cell23_7310603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 2, 3].length) (baseStart_7310603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310603 prefixEnd_7310603 := by exact prefixLift 7310603
  have htrace : WordTrace (prefixWord ++ tailWord_7310603) baseStart_7310603 baseEnd_7310603 := by
    simpa [prefixWord, tailWord_7310603, baseEnd_7310603] using wordTrace_append hprefix tailTrace_7310603
  have hstable : (prefixWord ++ tailWord_7310603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310603).length < 2 ^ (prefixWord ++ tailWord_7310603).sum := by decide
  have hdescent : baseEnd_7310603 < baseStart_7310603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310656 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2]
def baseStart_7310656 : Nat := 118140960795 + 7310656 * 2 ^ 59
def prefixEnd_7310656 : Nat := 4983230072969 + 3 ^ 40 * 7310656 * 2
def baseEnd_7310656 : Nat := 3753880427675854258478911

theorem tailTrace_7310656 : CollatzResearch.WordTrace tailWord_7310656 prefixEnd_7310656 3753880427675854258478911 := by
  unfold tailWord_7310656
  simp only [CollatzResearch.WordTrace]
  refine ⟨133320764901374673743459911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177761019868499564991279881 133320764901374673743459911)
  ·
    refine ⟨199981147352062010615189867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133320764901374673743459911 199981147352062010615189867)
    ·
      refine ⟨299971721028093015922784801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199981147352062010615189867 299971721028093015922784801)
      ·
        refine ⟨224978790771069761942088601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299971721028093015922784801 224978790771069761942088601)
        ·
          refine ⟨168734093078302321456566451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224978790771069761942088601 168734093078302321456566451)
          ·
            refine ⟨253101139617453482184849677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168734093078302321456566451 253101139617453482184849677)
            ·
              refine ⟨94912927356545055819318629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253101139617453482184849677 94912927356545055819318629)
              ·
                refine ⟨17796173879352197966122243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94912927356545055819318629 17796173879352197966122243)
                ·
                  refine ⟨26694260819028296949183365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796173879352197966122243 26694260819028296949183365)
                  ·
                    refine ⟨5005173903567805677971881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26694260819028296949183365 5005173903567805677971881)
                    ·
                      refine ⟨3753880427675854258478911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005173903567805677971881 3753880427675854258478911)
                      ·
                        rfl

theorem cell23_7310656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_7310656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310656 prefixEnd_7310656 := by exact prefixLift 7310656
  have htrace : WordTrace (prefixWord ++ tailWord_7310656) baseStart_7310656 baseEnd_7310656 := by
    simpa [prefixWord, tailWord_7310656, baseEnd_7310656] using wordTrace_append hprefix tailTrace_7310656
  have hstable : (prefixWord ++ tailWord_7310656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310656).length < 2 ^ (prefixWord ++ tailWord_7310656).sum := by decide
  have hdescent : baseEnd_7310656 < baseStart_7310656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310673 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_7310673 : Nat := 118140960795 + 7310673 * 2 ^ 59
def prefixEnd_7310673 : Nat := 4983230072969 + 3 ^ 40 * 7310673 * 2
def baseEnd_7310673 : Nat := 3753889156846980691966333

theorem tailTrace_7310673 : CollatzResearch.WordTrace tailWord_7310673 prefixEnd_7310673 3753889156846980691966333 := by
  unfold tailWord_7310673
  simp only [CollatzResearch.WordTrace]
  refine ⟨266642149843687759390288673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177761433229125172926859115 266642149843687759390288673)
  ·
    refine ⟨199981612382765819542716505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266642149843687759390288673 199981612382765819542716505)
    ·
      refine ⟨149986209287074364657037379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199981612382765819542716505 149986209287074364657037379)
      ·
        refine ⟨224979313930611546985556069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149986209287074364657037379 224979313930611546985556069)
        ·
          refine ⟨42183621361989665059791763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224979313930611546985556069 42183621361989665059791763)
          ·
            refine ⟨63275432042984497589687645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42183621361989665059791763 63275432042984497589687645)
            ·
              refine ⟨23728287016119186596132867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63275432042984497589687645 23728287016119186596132867)
              ·
                refine ⟨35592430524178779894199301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23728287016119186596132867 35592430524178779894199301)
                ·
                  refine ⟨6673580723283521230162369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35592430524178779894199301 6673580723283521230162369)
                  ·
                    refine ⟨5005185542462640922621777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673580723283521230162369 5005185542462640922621777)
                    ·
                      refine ⟨3753889156846980691966333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005185542462640922621777 3753889156846980691966333)
                      ·
                        rfl

theorem cell23_7310673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_7310673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310673 prefixEnd_7310673 := by exact prefixLift 7310673
  have htrace : WordTrace (prefixWord ++ tailWord_7310673) baseStart_7310673 baseEnd_7310673 := by
    simpa [prefixWord, tailWord_7310673, baseEnd_7310673] using wordTrace_append hprefix tailTrace_7310673
  have hstable : (prefixWord ++ tailWord_7310673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310673).length < 2 ^ (prefixWord ++ tailWord_7310673).sum := by decide
  have hdescent : baseEnd_7310673 < baseStart_7310673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310679 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 7]
def baseStart_7310679 : Nat := 118140960795 + 7310679 * 2 ^ 59
def prefixEnd_7310679 : Nat := 4983230072969 + 3 ^ 40 * 7310679 * 2
def baseEnd_7310679 : Nat := 417099137525656407610145

theorem tailTrace_7310679 : CollatzResearch.WordTrace tailWord_7310679 prefixEnd_7310679 417099137525656407610145 := by
  unfold tailWord_7310679
  simp only [CollatzResearch.WordTrace]
  refine ⟨266642368681666022415007091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177761579121110681610004727 266642368681666022415007091)
  ·
    refine ⟨399963553022499033622510637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266642368681666022415007091 399963553022499033622510637)
    ·
      refine ⟨149986332383437137608441489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399963553022499033622510637 149986332383437137608441489)
      ·
        refine ⟨112489749287577853206331117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149986332383437137608441489 112489749287577853206331117)
        ·
          refine ⟨42183655982841694952374169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112489749287577853206331117 42183655982841694952374169)
          ·
            refine ⟨31637741987131271214280627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42183655982841694952374169 31637741987131271214280627)
            ·
              refine ⟨47456612980696906821420941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31637741987131271214280627 47456612980696906821420941)
              ·
                refine ⟨17796229867761340058032853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47456612980696906821420941 17796229867761340058032853)
                ·
                  refine ⟨417099137525656407610145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17796229867761340058032853 417099137525656407610145)
                  ·
                    rfl

theorem cell23_7310679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 7].length) (baseStart_7310679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310679 prefixEnd_7310679 := by exact prefixLift 7310679
  have htrace : WordTrace (prefixWord ++ tailWord_7310679) baseStart_7310679 baseEnd_7310679 := by
    simpa [prefixWord, tailWord_7310679, baseEnd_7310679] using wordTrace_append hprefix tailTrace_7310679
  have hstable : (prefixWord ++ tailWord_7310679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310679).length < 2 ^ (prefixWord ++ tailWord_7310679).sum := by decide
  have hdescent : baseEnd_7310679 < baseStart_7310679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310746 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7310746 : Nat := 118140960795 + 7310746 * 2 ^ 59
def prefixEnd_7310746 : Nat := 4983230072969 + 3 ^ 40 * 7310746 * 2
def baseEnd_7310746 : Nat := 3753926640934758906353497

theorem tailTrace_7310746 : CollatzResearch.WordTrace tailWord_7310746 prefixEnd_7310746 3753926640934758906353497 := by
  unfold tailWord_7310746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66661203093105823214424023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177763208248282195238464061 66661203093105823214424023)
  ·
    refine ⟨99991804639658734821636035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66661203093105823214424023 99991804639658734821636035)
    ·
      refine ⟨149987706959488102232454053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99991804639658734821636035 149987706959488102232454053)
      ·
        refine ⟨28122695054904019168585135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149987706959488102232454053 28122695054904019168585135)
        ·
          refine ⟨42184042582356028752877703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28122695054904019168585135 42184042582356028752877703)
          ·
            refine ⟨63276063873534043129316555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42184042582356028752877703 63276063873534043129316555)
            ·
              refine ⟨94914095810301064693974833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63276063873534043129316555 94914095810301064693974833)
              ·
                refine ⟨71185571857725798520481125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94914095810301064693974833 71185571857725798520481125)
                ·
                  refine ⟨13347294723323587222590211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71185571857725798520481125 13347294723323587222590211)
                  ·
                    refine ⟨20020942084985380833885317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13347294723323587222590211 20020942084985380833885317)
                    ·
                      refine ⟨3753926640934758906353497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20020942084985380833885317 3753926640934758906353497)
                      ·
                        rfl

theorem cell23_7310746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7310746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310746 prefixEnd_7310746 := by exact prefixLift 7310746
  have htrace : WordTrace (prefixWord ++ tailWord_7310746) baseStart_7310746 baseEnd_7310746 := by
    simpa [prefixWord, tailWord_7310746, baseEnd_7310746] using wordTrace_append hprefix tailTrace_7310746
  have hstable : (prefixWord ++ tailWord_7310746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310746).length < 2 ^ (prefixWord ++ tailWord_7310746).sum := by decide
  have hdescent : baseEnd_7310746 < baseStart_7310746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310756 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_7310756 : Nat := 118140960795 + 7310756 * 2 ^ 59
def prefixEnd_7310756 : Nat := 4983230072969 + 3 ^ 40 * 7310756 * 2
def baseEnd_7310756 : Nat := 1251310591913767955742817

theorem tailTrace_7310756 : CollatzResearch.WordTrace tailWord_7310756 prefixEnd_7310756 1251310591913767955742817 := by
  unfold tailWord_7310756
  simp only [CollatzResearch.WordTrace]
  refine ⟨133322588551193532282780061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177763451401591376377040081 133322588551193532282780061)
  ·
    refine ⟨49995970706697574606042523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133322588551193532282780061 49995970706697574606042523)
    ·
      refine ⟨74993956060046361909063785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49995970706697574606042523 74993956060046361909063785)
      ·
        refine ⟨56245467045034771431797839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74993956060046361909063785 56245467045034771431797839)
        ·
          refine ⟨84368200567552157147696759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56245467045034771431797839 84368200567552157147696759)
          ·
            refine ⟨126552300851328235721545139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84368200567552157147696759 126552300851328235721545139)
            ·
              refine ⟨189828451276992353582317709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126552300851328235721545139 189828451276992353582317709)
              ·
                refine ⟨71185669228872132593369141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189828451276992353582317709 71185669228872132593369141)
                ·
                  refine ⟨6673656490206762430628357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71185669228872132593369141 6673656490206762430628357)
                  ·
                    refine ⟨1251310591913767955742817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673656490206762430628357 1251310591913767955742817)
                    ·
                      rfl

theorem cell23_7310756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_7310756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310756 prefixEnd_7310756 := by exact prefixLift 7310756
  have htrace : WordTrace (prefixWord ++ tailWord_7310756) baseStart_7310756 baseEnd_7310756 := by
    simpa [prefixWord, tailWord_7310756, baseEnd_7310756] using wordTrace_append hprefix tailTrace_7310756
  have hstable : (prefixWord ++ tailWord_7310756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310756).length < 2 ^ (prefixWord ++ tailWord_7310756).sum := by decide
  have hdescent : baseEnd_7310756 < baseStart_7310756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310760 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7310760 : Nat := 118140960795 + 7310760 * 2 ^ 59
def prefixEnd_7310760 : Nat := 4983230072969 + 3 ^ 40 * 7310760 * 2
def baseEnd_7310760 : Nat := 1251311276554640617192811

theorem tailTrace_7310760 : CollatzResearch.WordTrace tailWord_7310760 prefixEnd_7310760 1251311276554640617192811 := by
  unfold tailWord_7310760
  simp only [CollatzResearch.WordTrace]
  refine ⟨133322661497186286624352867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177763548662915048832470489 133322661497186286624352867)
  ·
    refine ⟨199983992245779429936529301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133322661497186286624352867 199983992245779429936529301)
    ·
      refine ⟨9374249636520910778274811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199983992245779429936529301 9374249636520910778274811)
      ·
        refine ⟨14061374454781366167412217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374249636520910778274811 14061374454781366167412217)
        ·
          refine ⟨10546030841086024625559163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14061374454781366167412217 10546030841086024625559163)
          ·
            refine ⟨15819046261629036938338745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546030841086024625559163 15819046261629036938338745)
            ·
              refine ⟨11864284696221777703754059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15819046261629036938338745 11864284696221777703754059)
              ·
                refine ⟨17796427044332666555631089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864284696221777703754059 17796427044332666555631089)
                ·
                  refine ⟨13347320283249499916723317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17796427044332666555631089 13347320283249499916723317)
                  ·
                    refine ⟨1251311276554640617192811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13347320283249499916723317 1251311276554640617192811)
                    ·
                      rfl

theorem cell23_7310760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7310760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310760 prefixEnd_7310760 := by exact prefixLift 7310760
  have htrace : WordTrace (prefixWord ++ tailWord_7310760) baseStart_7310760 baseEnd_7310760 := by
    simpa [prefixWord, tailWord_7310760, baseEnd_7310760] using wordTrace_append hprefix tailTrace_7310760
  have hstable : (prefixWord ++ tailWord_7310760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310760).length < 2 ^ (prefixWord ++ tailWord_7310760).sum := by decide
  have hdescent : baseEnd_7310760 < baseStart_7310760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310833 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_7310833 : Nat := 118140960795 + 7310833 * 2 ^ 59
def prefixEnd_7310833 : Nat := 4983230072969 + 3 ^ 40 * 7310833 * 2
def baseEnd_7310833 : Nat := 1251323771250566688655199

theorem tailTrace_7310833 : CollatzResearch.WordTrace tailWord_7310833 prefixEnd_7310833 1251323771250566688655199 := by
  unfold tailWord_7310833
  simp only [CollatzResearch.WordTrace]
  refine ⟨266647985523108106716113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177765323682072071144075435 266647985523108106716113153)
  ·
    refine ⟨199985989142331080037084865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266647985523108106716113153 199985989142331080037084865)
    ·
      refine ⟨149989491856748310027813649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199985989142331080037084865 149989491856748310027813649)
      ·
        refine ⟨112492118892561232520860237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149989491856748310027813649 112492118892561232520860237)
        ·
          refine ⟨42184544584710462195322589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112492118892561232520860237 42184544584710462195322589)
          ·
            refine ⟨15819204219266423323245971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42184544584710462195322589 15819204219266423323245971)
            ·
              refine ⟨23728806328899634984868957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15819204219266423323245971 23728806328899634984868957)
              ·
                refine ⟨8898302373337363119325859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23728806328899634984868957 8898302373337363119325859)
                ·
                  refine ⟨13347453560006044678988789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898302373337363119325859 13347453560006044678988789)
                  ·
                    refine ⟨1251323771250566688655199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13347453560006044678988789 1251323771250566688655199)
                    ·
                      rfl

theorem cell23_7310833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_7310833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310833 prefixEnd_7310833 := by exact prefixLift 7310833
  have htrace : WordTrace (prefixWord ++ tailWord_7310833) baseStart_7310833 baseEnd_7310833 := by
    simpa [prefixWord, tailWord_7310833, baseEnd_7310833] using wordTrace_append hprefix tailTrace_7310833
  have hstable : (prefixWord ++ tailWord_7310833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310833).length < 2 ^ (prefixWord ++ tailWord_7310833).sum := by decide
  have hdescent : baseEnd_7310833 < baseStart_7310833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310856 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7310856 : Nat := 118140960795 + 7310856 * 2 ^ 59
def prefixEnd_7310856 : Nat := 4983230072969 + 3 ^ 40 * 7310856 * 2
def baseEnd_7310856 : Nat := 3753983123806753475977991

theorem tailTrace_7310856 : CollatzResearch.WordTrace tailWord_7310856 prefixEnd_7310856 3753983123806753475977991 := by
  unfold tailWord_7310856
  simp only [CollatzResearch.WordTrace]
  refine ⟨133324412201012390822100211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177765882934683187762800281 133324412201012390822100211)
  ·
    refine ⟨199986618301518586233150317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133324412201012390822100211 199986618301518586233150317)
    ·
      refine ⟨74994981863069469837431369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199986618301518586233150317 74994981863069469837431369)
      ·
        refine ⟨56246236397302102378073527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74994981863069469837431369 56246236397302102378073527)
        ·
          refine ⟨84369354595953153567110291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56246236397302102378073527 84369354595953153567110291)
          ·
            refine ⟨126554031893929730350665437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84369354595953153567110291 126554031893929730350665437)
            ·
              refine ⟨47457761960223648881499539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126554031893929730350665437 47457761960223648881499539)
              ·
                refine ⟨71186642940335473322249309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47457761960223648881499539 71186642940335473322249309)
                ·
                  refine ⟨26694991102625802495843491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71186642940335473322249309 26694991102625802495843491)
                  ·
                    refine ⟨40042486653938703743765237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26694991102625802495843491 40042486653938703743765237)
                    ·
                      refine ⟨3753983123806753475977991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40042486653938703743765237 3753983123806753475977991)
                      ·
                        rfl

theorem cell23_7310856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7310856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310856 prefixEnd_7310856 := by exact prefixLift 7310856
  have htrace : WordTrace (prefixWord ++ tailWord_7310856) baseStart_7310856 baseEnd_7310856 := by
    simpa [prefixWord, tailWord_7310856, baseEnd_7310856] using wordTrace_append hprefix tailTrace_7310856
  have hstable : (prefixWord ++ tailWord_7310856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310856).length < 2 ^ (prefixWord ++ tailWord_7310856).sum := by decide
  have hdescent : baseEnd_7310856 < baseStart_7310856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310876 : List Nat := [2, 2, 3, 1, 2, 1, 3, 9]
def baseStart_7310876 : Nat := 118140960795 + 7310876 * 2 ^ 59
def prefixEnd_7310876 : Nat := 4983230072969 + 3 ^ 40 * 7310876 * 2
def baseEnd_7310876 : Nat := 139036792348883088804737

theorem tailTrace_7310876 : CollatzResearch.WordTrace tailWord_7310876 prefixEnd_7310876 139036792348883088804737 := by
  unfold tailWord_7310876
  simp only [CollatzResearch.WordTrace]
  refine ⟨133324776930976162529964241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177766369241301550039952321 133324776930976162529964241)
  ·
    refine ⟨99993582698232121897473181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133324776930976162529964241 99993582698232121897473181)
    ·
      refine ⟨37497593511837045711552443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99993582698232121897473181 37497593511837045711552443)
      ·
        refine ⟨56246390267755568567328665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37497593511837045711552443 56246390267755568567328665)
        ·
          refine ⟨42184792700816676425496499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56246390267755568567328665 42184792700816676425496499)
          ·
            refine ⟨63277189051225014638244749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42184792700816676425496499 63277189051225014638244749)
            ·
              refine ⟨23728945894209380489341781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63277189051225014638244749 23728945894209380489341781)
              ·
                refine ⟨139036792348883088804737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23728945894209380489341781 139036792348883088804737)
                ·
                  rfl

theorem cell23_7310876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 9].length) (baseStart_7310876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310876 prefixEnd_7310876 := by exact prefixLift 7310876
  have htrace : WordTrace (prefixWord ++ tailWord_7310876) baseStart_7310876 baseEnd_7310876 := by
    simpa [prefixWord, tailWord_7310876, baseEnd_7310876] using wordTrace_append hprefix tailTrace_7310876
  have hstable : (prefixWord ++ tailWord_7310876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310876).length < 2 ^ (prefixWord ++ tailWord_7310876).sum := by decide
  have hdescent : baseEnd_7310876 < baseStart_7310876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310890 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7310890 : Nat := 118140960795 + 7310890 * 2 ^ 59
def prefixEnd_7310890 : Nat := 4983230072969 + 3 ^ 40 * 7310890 * 2
def baseEnd_7310890 : Nat := 3754000582149006342952835

theorem tailTrace_7310890 : CollatzResearch.WordTrace tailWord_7310890 prefixEnd_7310890 3754000582149006342952835 := by
  unfold tailWord_7310890
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662516120975401362734531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177766709655934403633958749 66662516120975401362734531)
  ·
    refine ⟨99993774181463102044101797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66662516120975401362734531 99993774181463102044101797)
    ·
      refine ⟨18748832659024331633269087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99993774181463102044101797 18748832659024331633269087)
      ·
        refine ⟨28123248988536497449903631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18748832659024331633269087 28123248988536497449903631)
        ·
          refine ⟨42184873482804746174855447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123248988536497449903631 42184873482804746174855447)
          ·
            refine ⟨63277310224207119262283171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42184873482804746174855447 63277310224207119262283171)
            ·
              refine ⟨94915965336310678893424757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63277310224207119262283171 94915965336310678893424757)
              ·
                refine ⟨8898371750279126146258571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94915965336310678893424757 8898371750279126146258571)
                ·
                  refine ⟨13347557625418689219387857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898371750279126146258571 13347557625418689219387857)
                  ·
                    refine ⟨10010668219064016914540893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347557625418689219387857 10010668219064016914540893)
                    ·
                      refine ⟨3754000582149006342952835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10010668219064016914540893 3754000582149006342952835)
                      ·
                        rfl

theorem cell23_7310890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7310890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310890 prefixEnd_7310890 := by exact prefixLift 7310890
  have htrace : WordTrace (prefixWord ++ tailWord_7310890) baseStart_7310890 baseEnd_7310890 := by
    simpa [prefixWord, tailWord_7310890, baseEnd_7310890] using wordTrace_append hprefix tailTrace_7310890
  have hstable : (prefixWord ++ tailWord_7310890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310890).length < 2 ^ (prefixWord ++ tailWord_7310890).sum := by decide
  have hdescent : baseEnd_7310890 < baseStart_7310890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310906 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_7310906 : Nat := 118140960795 + 7310906 * 2 ^ 59
def prefixEnd_7310906 : Nat := 4983230072969 + 3 ^ 40 * 7310906 * 2
def baseEnd_7310906 : Nat := 1251336265946492760117587

theorem tailTrace_7310906 : CollatzResearch.WordTrace tailWord_7310906 prefixEnd_7310906 1251336265946492760117587 := by
  unfold tailWord_7310906
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662662012960910045880143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177767098701229093455680381 66662662012960910045880143)
  ·
    refine ⟨99993993019441365068820215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66662662012960910045880143 99993993019441365068820215)
    ·
      refine ⟨149990989529162047603230323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99993993019441365068820215 149990989529162047603230323)
      ·
        refine ⟨224986484293743071404845485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149990989529162047603230323 224986484293743071404845485)
        ·
          refine ⟨84369931610153651776817057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224986484293743071404845485 84369931610153651776817057)
          ·
            refine ⟨63277448707615238832612793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84369931610153651776817057 63277448707615238832612793)
            ·
              refine ⟨47458086530711429124459595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63277448707615238832612793 47458086530711429124459595)
              ·
                refine ⟨71187129796067143686689393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47458086530711429124459595 71187129796067143686689393)
                ·
                  refine ⟨53390347347050357765017045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71187129796067143686689393 53390347347050357765017045)
                  ·
                    refine ⟨1251336265946492760117587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53390347347050357765017045 1251336265946492760117587)
                    ·
                      rfl

theorem cell23_7310906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_7310906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310906 prefixEnd_7310906 := by exact prefixLift 7310906
  have htrace : WordTrace (prefixWord ++ tailWord_7310906) baseStart_7310906 baseEnd_7310906 := by
    simpa [prefixWord, tailWord_7310906, baseEnd_7310906] using wordTrace_append hprefix tailTrace_7310906
  have hstable : (prefixWord ++ tailWord_7310906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310906).length < 2 ^ (prefixWord ++ tailWord_7310906).sum := by decide
  have hdescent : baseEnd_7310906 < baseStart_7310906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310926 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7310926 : Nat := 118140960795 + 7310926 * 2 ^ 59
def prefixEnd_7310926 : Nat := 4983230072969 + 3 ^ 40 * 7310926 * 2
def baseEnd_7310926 : Nat := 3754019067452568202102669

theorem tailTrace_7310926 : CollatzResearch.WordTrace tailWord_7310926 prefixEnd_7310926 3754019067452568202102669 := by
  unfold tailWord_7310926
  simp only [CollatzResearch.WordTrace]
  refine ⟨33331422188971397949906079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177767585007847455732832421 33331422188971397949906079)
  ·
    refine ⟨49997133283457096924859119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33331422188971397949906079 49997133283457096924859119)
    ·
      refine ⟨74995699925185645387288679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49997133283457096924859119 74995699925185645387288679)
      ·
        refine ⟨112493549887778468080933019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74995699925185645387288679 112493549887778468080933019)
        ·
          refine ⟨168740324831667702121399529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112493549887778468080933019 168740324831667702121399529)
          ·
            refine ⟨126555243623750776591049647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168740324831667702121399529 126555243623750776591049647)
            ·
              refine ⟨189832865435626164886574471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126555243623750776591049647 189832865435626164886574471)
              ·
                refine ⟨284749298153439247329861707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189832865435626164886574471 284749298153439247329861707)
                ·
                  refine ⟨427123947230158870994792561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284749298153439247329861707 427123947230158870994792561)
                  ·
                    refine ⟨320342960422619153246094421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427123947230158870994792561 320342960422619153246094421)
                    ·
                      refine ⟨3754019067452568202102669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320342960422619153246094421 3754019067452568202102669)
                      ·
                        rfl

theorem cell23_7310926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7310926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310926 prefixEnd_7310926 := by exact prefixLift 7310926
  have htrace : WordTrace (prefixWord ++ tailWord_7310926) baseStart_7310926 baseEnd_7310926 := by
    simpa [prefixWord, tailWord_7310926, baseEnd_7310926] using wordTrace_append hprefix tailTrace_7310926
  have hstable : (prefixWord ++ tailWord_7310926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310926).length < 2 ^ (prefixWord ++ tailWord_7310926).sum := by decide
  have hdescent : baseEnd_7310926 < baseStart_7310926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310934 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7310934 : Nat := 118140960795 + 7310934 * 2 ^ 59
def prefixEnd_7310934 : Nat := 4983230072969 + 3 ^ 40 * 7310934 * 2
def baseEnd_7310934 : Nat := 3754023175297804170802633

theorem tailTrace_7310934 : CollatzResearch.WordTrace tailWord_7310934 prefixEnd_7310934 3754023175297804170802633 := by
  unfold tailWord_7310934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16665729330983887560346241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177767779530494800643693237 16665729330983887560346241)
  ·
    refine ⟨12499296998237915670259681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16665729330983887560346241 12499296998237915670259681)
    ·
      refine ⟨9374472748678436752694761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12499296998237915670259681 9374472748678436752694761)
      ·
        refine ⟨7030854561508827564521071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9374472748678436752694761 7030854561508827564521071)
        ·
          refine ⟨10546281842263241346781607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030854561508827564521071 10546281842263241346781607)
          ·
            refine ⟨15819422763394862020172411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546281842263241346781607 15819422763394862020172411)
            ·
              refine ⟨23729134145092293030258617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15819422763394862020172411 23729134145092293030258617)
              ·
                refine ⟨17796850608819219772693963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23729134145092293030258617 17796850608819219772693963)
                ·
                  refine ⟨26695275913228829659040945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796850608819219772693963 26695275913228829659040945)
                  ·
                    refine ⟨20021456934921622244280709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26695275913228829659040945 20021456934921622244280709)
                    ·
                      refine ⟨3754023175297804170802633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20021456934921622244280709 3754023175297804170802633)
                      ·
                        rfl

theorem cell23_7310934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7310934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310934 prefixEnd_7310934 := by exact prefixLift 7310934
  have htrace : WordTrace (prefixWord ++ tailWord_7310934) baseStart_7310934 baseEnd_7310934 := by
    simpa [prefixWord, tailWord_7310934, baseEnd_7310934] using wordTrace_append hprefix tailTrace_7310934
  have hstable : (prefixWord ++ tailWord_7310934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310934).length < 2 ^ (prefixWord ++ tailWord_7310934).sum := by decide
  have hdescent : baseEnd_7310934 < baseStart_7310934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310936 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_7310936 : Nat := 118140960795 + 7310936 * 2 ^ 59
def prefixEnd_7310936 : Nat := 4983230072969 + 3 ^ 40 * 7310936 * 2
def baseEnd_7310936 : Nat := 1251341400753037720992541

theorem tailTrace_7310936 : CollatzResearch.WordTrace tailWord_7310936 prefixEnd_7310936 1251341400753037720992541 := by
  unfold tailWord_7310936
  simp only [CollatzResearch.WordTrace]
  refine ⟨133325871120867477653556331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177767828161156636871408441 133325871120867477653556331)
  ·
    refine ⟨199988806681301216480334497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133325871120867477653556331 199988806681301216480334497)
    ·
      refine ⟨149991605010975912360250873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199988806681301216480334497 149991605010975912360250873)
      ·
        refine ⟨112493703758231934270188155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149991605010975912360250873 112493703758231934270188155)
        ·
          refine ⟨168740555637347901405282233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112493703758231934270188155 168740555637347901405282233)
          ·
            refine ⟨126555416728010926053961675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168740555637347901405282233 126555416728010926053961675)
            ·
              refine ⟨189833125092016389080942513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126555416728010926053961675 189833125092016389080942513)
              ·
                refine ⟨142374843819012291810706885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189833125092016389080942513 142374843819012291810706885)
                ·
                  refine ⟨26695283216064804714507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142374843819012291810706885 26695283216064804714507541)
                  ·
                    refine ⟨1251341400753037720992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26695283216064804714507541 1251341400753037720992541)
                    ·
                      rfl

theorem cell23_7310936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_7310936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310936 prefixEnd_7310936 := by exact prefixLift 7310936
  have htrace : WordTrace (prefixWord ++ tailWord_7310936) baseStart_7310936 baseEnd_7310936 := by
    simpa [prefixWord, tailWord_7310936, baseEnd_7310936] using wordTrace_append hprefix tailTrace_7310936
  have hstable : (prefixWord ++ tailWord_7310936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310936).length < 2 ^ (prefixWord ++ tailWord_7310936).sum := by decide
  have hdescent : baseEnd_7310936 < baseStart_7310936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310941 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7310941 : Nat := 118140960795 + 7310941 * 2 ^ 59
def prefixEnd_7310941 : Nat := 4983230072969 + 3 ^ 40 * 7310941 * 2
def baseEnd_7310941 : Nat := 3754026769662385643415101

theorem tailTrace_7310941 : CollatzResearch.WordTrace tailWord_7310941 prefixEnd_7310941 3754026769662385643415101 := by
  unfold tailWord_7310941
  simp only [CollatzResearch.WordTrace]
  refine ⟨266651924606716841161044677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177767949737811227440696451 266651924606716841161044677)
  ·
    refine ⟨49997235863759407717695877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266651924606716841161044677 49997235863759407717695877)
    ·
      refine ⟨9374481724454888947067977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49997235863759407717695877 9374481724454888947067977)
      ·
        refine ⟨7030861293341166710300983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9374481724454888947067977 7030861293341166710300983)
        ·
          refine ⟨10546291940011750065451475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030861293341166710300983 10546291940011750065451475)
          ·
            refine ⟨15819437910017625098177213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546291940011750065451475 15819437910017625098177213)
            ·
              refine ⟨5932289216256609411816455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15819437910017625098177213 5932289216256609411816455)
              ·
                refine ⟨8898433824384914117724683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932289216256609411816455 8898433824384914117724683)
                ·
                  refine ⟨13347650736577371176587025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898433824384914117724683 13347650736577371176587025)
                  ·
                    refine ⟨10010738052433028382440269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347650736577371176587025 10010738052433028382440269)
                    ·
                      refine ⟨3754026769662385643415101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10010738052433028382440269 3754026769662385643415101)
                      ·
                        rfl

theorem cell23_7310941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7310941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310941 prefixEnd_7310941 := by exact prefixLift 7310941
  have htrace : WordTrace (prefixWord ++ tailWord_7310941) baseStart_7310941 baseEnd_7310941 := by
    simpa [prefixWord, tailWord_7310941, baseEnd_7310941] using wordTrace_append hprefix tailTrace_7310941
  have hstable : (prefixWord ++ tailWord_7310941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310941).length < 2 ^ (prefixWord ++ tailWord_7310941).sum := by decide
  have hdescent : baseEnd_7310941 < baseStart_7310941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310956 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7310956 : Nat := 118140960795 + 7310956 * 2 ^ 59
def prefixEnd_7310956 : Nat := 4983230072969 + 3 ^ 40 * 7310956 * 2
def baseEnd_7310956 : Nat := 3754034471872203084727531

theorem tailTrace_7310956 : CollatzResearch.WordTrace tailWord_7310956 prefixEnd_7310956 3754034471872203084727531 := by
  unfold tailWord_7310956
  simp only [CollatzResearch.WordTrace]
  refine ⟨133326235850831249361420361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177768314467774999148560481 133326235850831249361420361)
  ·
    refine ⟨99994676888123437021065271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133326235850831249361420361 99994676888123437021065271)
    ·
      refine ⟨149992015332185155531597907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99994676888123437021065271 149992015332185155531597907)
      ·
        refine ⟨224988022998277733297396861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149992015332185155531597907 224988022998277733297396861)
        ·
          refine ⟨84370508624354149986523823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224988022998277733297396861 84370508624354149986523823)
          ·
            refine ⟨126555762936531224979785735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84370508624354149986523823 126555762936531224979785735)
            ·
              refine ⟨189833644404796837469678603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126555762936531224979785735 189833644404796837469678603)
              ·
                refine ⟨284750466607195256204517905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189833644404796837469678603 284750466607195256204517905)
                ·
                  refine ⟨213562849955396442153388429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284750466607195256204517905 213562849955396442153388429)
                  ·
                    refine ⟨80086068733273665807520661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213562849955396442153388429 80086068733273665807520661)
                    ·
                      refine ⟨3754034471872203084727531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80086068733273665807520661 3754034471872203084727531)
                      ·
                        rfl

theorem cell23_7310956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7310956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310956 prefixEnd_7310956 := by exact prefixLift 7310956
  have htrace : WordTrace (prefixWord ++ tailWord_7310956) baseStart_7310956 baseEnd_7310956 := by
    simpa [prefixWord, tailWord_7310956, baseEnd_7310956] using wordTrace_append hprefix tailTrace_7310956
  have hstable : (prefixWord ++ tailWord_7310956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310956).length < 2 ^ (prefixWord ++ tailWord_7310956).sum := by decide
  have hdescent : baseEnd_7310956 < baseStart_7310956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310973 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_7310973 : Nat := 118140960795 + 7310973 * 2 ^ 59
def prefixEnd_7310973 : Nat := 4983230072969 + 3 ^ 40 * 7310973 * 2
def baseEnd_7310973 : Nat := 3754043201043329518214953

theorem tailTrace_7310973 : CollatzResearch.WordTrace tailWord_7310973 prefixEnd_7310973 3754043201043329518214953 := by
  unfold tailWord_7310973
  simp only [CollatzResearch.WordTrace]
  refine ⟨266653091742600910626209573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177768727828400607084139715 266653091742600910626209573)
  ·
    refine ⟨49997454701737670742414295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266653091742600910626209573 49997454701737670742414295)
    ·
      refine ⟨74996182052606506113621443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49997454701737670742414295 74996182052606506113621443)
      ·
        refine ⟨112494273078909759170432165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74996182052606506113621443 112494273078909759170432165)
        ·
          refine ⟨21092676202295579844456031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112494273078909759170432165 21092676202295579844456031)
          ·
            refine ⟨31639014303443369766684047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21092676202295579844456031 31639014303443369766684047)
            ·
              refine ⟨47458521455165054650026071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31639014303443369766684047 47458521455165054650026071)
              ·
                refine ⟨71187782182747581975039107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47458521455165054650026071 71187782182747581975039107)
                ·
                  refine ⟨106781673274121372962558661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71187782182747581975039107 106781673274121372962558661)
                  ·
                    refine ⟨20021563738897757430479749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106781673274121372962558661 20021563738897757430479749)
                    ·
                      refine ⟨3754043201043329518214953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20021563738897757430479749 3754043201043329518214953)
                      ·
                        rfl

theorem cell23_7310973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_7310973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310973 prefixEnd_7310973 := by exact prefixLift 7310973
  have htrace : WordTrace (prefixWord ++ tailWord_7310973) baseStart_7310973 baseEnd_7310973 := by
    simpa [prefixWord, tailWord_7310973, baseEnd_7310973] using wordTrace_append hprefix tailTrace_7310973
  have hstable : (prefixWord ++ tailWord_7310973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310973).length < 2 ^ (prefixWord ++ tailWord_7310973).sum := by decide
  have hdescent : baseEnd_7310973 < baseStart_7310973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310977 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7310977 : Nat := 118140960795 + 7310977 * 2 ^ 59
def prefixEnd_7310977 : Nat := 4983230072969 + 3 ^ 40 * 7310977 * 2
def baseEnd_7310977 : Nat := 3754045254965947502564935

theorem tailTrace_7310977 : CollatzResearch.WordTrace tailWord_7310977 prefixEnd_7310977 3754045254965947502564935 := by
  unfold tailWord_7310977
  simp only [CollatzResearch.WordTrace]
  refine ⟨266653237634586419309355185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177768825089724279539570123 266653237634586419309355185)
  ·
    refine ⟨199989928225939814482016389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266653237634586419309355185 199989928225939814482016389)
    ·
      refine ⟨37498111542363715215378073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199989928225939814482016389 37498111542363715215378073)
      ·
        refine ⟨28123583656772786411533555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37498111542363715215378073 28123583656772786411533555)
        ·
          refine ⟨42185375485159179617300333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123583656772786411533555 42185375485159179617300333)
          ·
            refine ⟨15819515806934692356487625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42185375485159179617300333 15819515806934692356487625)
            ·
              refine ⟨11864636855201019267365719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15819515806934692356487625 11864636855201019267365719)
              ·
                refine ⟨17796955282801528901048579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864636855201019267365719 17796955282801528901048579)
                ·
                  refine ⟨26695432924202293351572869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796955282801528901048579 26695432924202293351572869)
                  ·
                    refine ⟨5005393673287930003419913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26695432924202293351572869 5005393673287930003419913)
                    ·
                      refine ⟨3754045254965947502564935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005393673287930003419913 3754045254965947502564935)
                      ·
                        rfl

theorem cell23_7310977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7310977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310977 prefixEnd_7310977 := by exact prefixLift 7310977
  have htrace : WordTrace (prefixWord ++ tailWord_7310977) baseStart_7310977 baseEnd_7310977 := by
    simpa [prefixWord, tailWord_7310977, baseEnd_7310977] using wordTrace_append hprefix tailTrace_7310977
  have hstable : (prefixWord ++ tailWord_7310977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310977).length < 2 ^ (prefixWord ++ tailWord_7310977).sum := by decide
  have hdescent : baseEnd_7310977 < baseStart_7310977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7310983 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 7]
def baseStart_7310983 : Nat := 118140960795 + 7310983 * 2 ^ 59
def prefixEnd_7310983 : Nat := 4983230072969 + 3 ^ 40 * 7310983 * 2
def baseEnd_7310983 : Nat := 417116481761097164343323

theorem tailTrace_7310983 : CollatzResearch.WordTrace tailWord_7310983 prefixEnd_7310983 417116481761097164343323 := by
  unfold tailWord_7310983
  simp only [CollatzResearch.WordTrace]
  refine ⟨266653456472564682334073603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177768970981709788222715735 266653456472564682334073603)
  ·
    refine ⟨399980184708847023501110405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266653456472564682334073603 399980184708847023501110405)
    ·
      refine ⟨74996284632908816906458201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399980184708847023501110405 74996284632908816906458201)
      ·
        refine ⟨56247213474681612679843651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74996284632908816906458201 56247213474681612679843651)
        ·
          refine ⟨84370820212022419019765477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247213474681612679843651 84370820212022419019765477)
          ·
            refine ⟨15819528789754203566206027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84370820212022419019765477 15819528789754203566206027)
            ·
              refine ⟨23729293184631305349309041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15819528789754203566206027 23729293184631305349309041)
              ·
                refine ⟨17796969888473479011981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23729293184631305349309041 17796969888473479011981781)
                ·
                  refine ⟨417116481761097164343323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17796969888473479011981781 417116481761097164343323)
                  ·
                    rfl

theorem cell23_7310983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 7].length) (baseStart_7310983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7310983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7310983 prefixEnd_7310983 := by exact prefixLift 7310983
  have htrace : WordTrace (prefixWord ++ tailWord_7310983) baseStart_7310983 baseEnd_7310983 := by
    simpa [prefixWord, tailWord_7310983, baseEnd_7310983] using wordTrace_append hprefix tailTrace_7310983
  have hstable : (prefixWord ++ tailWord_7310983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7310983).length < 2 ^ (prefixWord ++ tailWord_7310983).sum := by decide
  have hdescent : baseEnd_7310983 < baseStart_7310983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7310983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311000 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 5]
def baseStart_7311000 : Nat := 118140960795 + 7311000 * 2 ^ 59
def prefixEnd_7311000 : Nat := 4983230072969 + 3 ^ 40 * 7311000 * 2
def baseEnd_7311000 : Nat := 417117451669000101397481

theorem tailTrace_7311000 : CollatzResearch.WordTrace tailWord_7311000 prefixEnd_7311000 417117451669000101397481 := by
  unfold tailWord_7311000
  simp only [CollatzResearch.WordTrace]
  refine ⟨133327038256751547118721227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177769384342335396158294969 133327038256751547118721227)
  ·
    refine ⟨199990557385127320678081841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133327038256751547118721227 199990557385127320678081841)
    ·
      refine ⟨149992918038845490508561381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199990557385127320678081841 149992918038845490508561381)
      ·
        refine ⟨28123672132283529470355259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149992918038845490508561381 28123672132283529470355259)
        ·
          refine ⟨42185508198425294205532889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123672132283529470355259 42185508198425294205532889)
          ·
            refine ⟨31639131148818970654149667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42185508198425294205532889 31639131148818970654149667)
            ·
              refine ⟨47458696723228455981224501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31639131148818970654149667 47458696723228455981224501)
              ·
                refine ⟨4449252817802667748239797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47458696723228455981224501 4449252817802667748239797)
                ·
                  refine ⟨417117451669000101397481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449252817802667748239797 417117451669000101397481)
                  ·
                    rfl

theorem cell23_7311000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 5].length) (baseStart_7311000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311000 prefixEnd_7311000 := by exact prefixLift 7311000
  have htrace : WordTrace (prefixWord ++ tailWord_7311000) baseStart_7311000 baseEnd_7311000 := by
    simpa [prefixWord, tailWord_7311000, baseEnd_7311000] using wordTrace_append hprefix tailTrace_7311000
  have hstable : (prefixWord ++ tailWord_7311000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311000).length < 2 ^ (prefixWord ++ tailWord_7311000).sum := by decide
  have hdescent : baseEnd_7311000 < baseStart_7311000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311013 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_7311013 : Nat := 118140960795 + 7311013 * 2 ^ 59
def prefixEnd_7311013 : Nat := 4983230072969 + 3 ^ 40 * 7311013 * 2
def baseEnd_7311013 : Nat := 1251354580089836453904923

theorem tailTrace_7311013 : CollatzResearch.WordTrace tailWord_7311013 prefixEnd_7311013 1251354580089836453904923 := by
  unfold tailWord_7311013
  simp only [CollatzResearch.WordTrace]
  refine ⟨266654550662455997457665693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177769700441637331638443795 266654550662455997457665693)
  ·
    refine ⟨99995456498420999046624635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266654550662455997457665693 99995456498420999046624635)
    ·
      refine ⟨149993184747631498569936953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99995456498420999046624635 149993184747631498569936953)
      ·
        refine ⟨112494888560723623927452715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149993184747631498569936953 112494888560723623927452715)
        ·
          refine ⟨168742332841085435891179073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112494888560723623927452715 168742332841085435891179073)
          ·
            refine ⟨126556749630814076918384305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168742332841085435891179073 126556749630814076918384305)
            ·
              refine ⟨94917562223110557688788229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126556749630814076918384305 94917562223110557688788229)
              ·
                refine ⟨17797042916833229566647793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94917562223110557688788229 17797042916833229566647793)
                ·
                  refine ⟨13347782187624922174985845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17797042916833229566647793 13347782187624922174985845)
                  ·
                    refine ⟨1251354580089836453904923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13347782187624922174985845 1251354580089836453904923)
                    ·
                      rfl

theorem cell23_7311013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_7311013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311013 prefixEnd_7311013 := by exact prefixLift 7311013
  have htrace : WordTrace (prefixWord ++ tailWord_7311013) baseStart_7311013 baseEnd_7311013 := by
    simpa [prefixWord, tailWord_7311013, baseEnd_7311013] using wordTrace_append hprefix tailTrace_7311013
  have hstable : (prefixWord ++ tailWord_7311013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311013).length < 2 ^ (prefixWord ++ tailWord_7311013).sum := by decide
  have hdescent : baseEnd_7311013 < baseStart_7311013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311033 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7311033 : Nat := 118140960795 + 7311033 * 2 ^ 59
def prefixEnd_7311033 : Nat := 4983230072969 + 3 ^ 40 * 7311033 * 2
def baseEnd_7311033 : Nat := 3754074009882599283464677

theorem tailTrace_7311033 : CollatzResearch.WordTrace tailWord_7311033 prefixEnd_7311033 3754074009882599283464677 := by
  unfold tailWord_7311033
  simp only [CollatzResearch.WordTrace]
  refine ⟨266655280122383540873393753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177770186748255693915595835 266655280122383540873393753)
  ·
    refine ⟨199991460091787655655045315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266655280122383540873393753 199991460091787655655045315)
    ·
      refine ⟨299987190137681483482567973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199991460091787655655045315 299987190137681483482567973)
      ·
        refine ⟨56247598150815278152981495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299987190137681483482567973 56247598150815278152981495)
        ·
          refine ⟨84371397226222917229472243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247598150815278152981495 84371397226222917229472243)
          ·
            refine ⟨126557095839334375844208365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84371397226222917229472243 126557095839334375844208365)
            ·
              refine ⟨47458910939750390941578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126557095839334375844208365 47458910939750390941578137)
              ·
                refine ⟨35594183204812793206183603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47458910939750390941578137 35594183204812793206183603)
                ·
                  refine ⟨53391274807219189809275405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35594183204812793206183603 53391274807219189809275405)
                  ·
                    refine ⟨20021728052707196178478277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53391274807219189809275405 20021728052707196178478277)
                    ·
                      refine ⟨3754074009882599283464677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20021728052707196178478277 3754074009882599283464677)
                      ·
                        rfl

theorem cell23_7311033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7311033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311033 prefixEnd_7311033 := by exact prefixLift 7311033
  have htrace : WordTrace (prefixWord ++ tailWord_7311033) baseStart_7311033 baseEnd_7311033 := by
    simpa [prefixWord, tailWord_7311033, baseEnd_7311033] using wordTrace_append hprefix tailTrace_7311033
  have hstable : (prefixWord ++ tailWord_7311033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311033).length < 2 ^ (prefixWord ++ tailWord_7311033).sum := by decide
  have hdescent : baseEnd_7311033 < baseStart_7311033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311090 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_7311090 : Nat := 118140960795 + 7311090 * 2 ^ 59
def prefixEnd_7311090 : Nat := 4983230072969 + 3 ^ 40 * 7311090 * 2
def baseEnd_7311090 : Nat := 417122586475545062272435

theorem tailTrace_7311090 : CollatzResearch.WordTrace tailWord_7311090 prefixEnd_7311090 417122586475545062272435 := by
  unfold tailWord_7311090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66664339770794259902054681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177771572722118026405479149 66664339770794259902054681)
  ·
    refine ⟨49998254828095694926541011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66664339770794259902054681 49998254828095694926541011)
    ·
      refine ⟨74997382242143542389811517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49998254828095694926541011 74997382242143542389811517)
      ·
        refine ⟨28124018340803828396179319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74997382242143542389811517 28124018340803828396179319)
        ·
          refine ⟨42186027511205742594268979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28124018340803828396179319 42186027511205742594268979)
          ·
            refine ⟨63279041266808613891403469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42186027511205742594268979 63279041266808613891403469)
            ·
              refine ⟨23729640475053230209276301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63279041266808613891403469 23729640475053230209276301)
              ·
                refine ⟨8898615178144961328478613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23729640475053230209276301 8898615178144961328478613)
                ·
                  refine ⟨417122586475545062272435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8898615178144961328478613 417122586475545062272435)
                  ·
                    rfl

theorem cell23_7311090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_7311090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311090 prefixEnd_7311090 := by exact prefixLift 7311090
  have htrace : WordTrace (prefixWord ++ tailWord_7311090) baseStart_7311090 baseEnd_7311090 := by
    simpa [prefixWord, tailWord_7311090, baseEnd_7311090] using wordTrace_append hprefix tailTrace_7311090
  have hstable : (prefixWord ++ tailWord_7311090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311090).length < 2 ^ (prefixWord ++ tailWord_7311090).sum := by decide
  have hdescent : baseEnd_7311090 < baseStart_7311090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311177 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_7311177 : Nat := 118140960795 + 7311177 * 2 ^ 59
def prefixEnd_7311177 : Nat := 4983230072969 + 3 ^ 40 * 7311177 * 2
def baseEnd_7311177 : Nat := 3754147951096846720064015

theorem tailTrace_7311177 : CollatzResearch.WordTrace tailWord_7311177 prefixEnd_7311177 3754147951096846720064015 := by
  unfold tailWord_7311177
  simp only [CollatzResearch.WordTrace]
  refine ⟨266660532233861853466635785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177773688155907902311090523 266660532233861853466635785)
  ·
    refine ⟨199995399175396390099976839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266660532233861853466635785 199995399175396390099976839)
    ·
      refine ⟨299993098763094585149965259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199995399175396390099976839 299993098763094585149965259)
      ·
        refine ⟨449989648144641877724947889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299993098763094585149965259 449989648144641877724947889)
        ·
          refine ⟨337492236108481408293710917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449989648144641877724947889 337492236108481408293710917)
          ·
            refine ⟨63279794270340264055070797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337492236108481408293710917 63279794270340264055070797)
            ·
              refine ⟨23729922851377599020651549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63279794270340264055070797 23729922851377599020651549)
              ·
                refine ⟨8898721069266599632744331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23729922851377599020651549 8898721069266599632744331)
                ·
                  refine ⟨13348081603899899449116497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898721069266599632744331 13348081603899899449116497)
                  ·
                    refine ⟨10011061202924924586837373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13348081603899899449116497 10011061202924924586837373)
                    ·
                      refine ⟨3754147951096846720064015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10011061202924924586837373 3754147951096846720064015)
                      ·
                        rfl

theorem cell23_7311177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_7311177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311177 prefixEnd_7311177 := by exact prefixLift 7311177
  have htrace : WordTrace (prefixWord ++ tailWord_7311177) baseStart_7311177 baseEnd_7311177 := by
    simpa [prefixWord, tailWord_7311177, baseEnd_7311177] using wordTrace_append hprefix tailTrace_7311177
  have hstable : (prefixWord ++ tailWord_7311177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311177).length < 2 ^ (prefixWord ++ tailWord_7311177).sum := by decide
  have hdescent : baseEnd_7311177 < baseStart_7311177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311180 : List Nat := [2, 2, 1, 3, 4, 1, 10]
def baseStart_7311180 : Nat := 118140960795 + 7311180 * 2 ^ 59
def prefixEnd_7311180 : Nat := 4983230072969 + 3 ^ 40 * 7311180 * 2
def baseEnd_7311180 : Nat := 46347524586898891460821

theorem tailTrace_7311180 : CollatzResearch.WordTrace tailWord_7311180 prefixEnd_7311180 46347524586898891460821 := by
  unfold tailWord_7311180
  simp only [CollatzResearch.WordTrace]
  refine ⟨133330320826425492489497497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177773761101900656652663329 133330320826425492489497497)
  ·
    refine ⟨99997740619819119367123123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133330320826425492489497497 99997740619819119367123123)
    ·
      refine ⟨149996610929728679050684685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99997740619819119367123123 149996610929728679050684685)
      ·
        refine ⟨56248729098648254644006757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149996610929728679050684685 56248729098648254644006757)
        ·
          refine ⟨10546636705996547745751267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56248729098648254644006757 10546636705996547745751267)
          ·
            refine ⟨15819955058994821618626901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546636705996547745751267 15819955058994821618626901)
            ·
              refine ⟨46347524586898891460821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15819955058994821618626901 46347524586898891460821)
              ·
                rfl

theorem cell23_7311180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 10].length) (baseStart_7311180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311180 prefixEnd_7311180 := by exact prefixLift 7311180
  have htrace : WordTrace (prefixWord ++ tailWord_7311180) baseStart_7311180 baseEnd_7311180 := by
    simpa [prefixWord, tailWord_7311180, baseEnd_7311180] using wordTrace_append hprefix tailTrace_7311180
  have hstable : (prefixWord ++ tailWord_7311180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311180).length < 2 ^ (prefixWord ++ tailWord_7311180).sum := by decide
  have hdescent : baseEnd_7311180 < baseStart_7311180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311191 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_7311191 : Nat := 118140960795 + 7311191 * 2 ^ 59
def prefixEnd_7311191 : Nat := 4983230072969 + 3 ^ 40 * 7311191 * 2
def baseEnd_7311191 : Nat := 3754155139826009665288951

theorem tailTrace_7311191 : CollatzResearch.WordTrace tailWord_7311191 prefixEnd_7311191 3754155139826009665288951 := by
  unfold tailWord_7311191
  simp only [CollatzResearch.WordTrace]
  refine ⟨266661042855811133857645427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177774028570540755905096951 266661042855811133857645427)
  ·
    refine ⟨399991564283716700786468141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266661042855811133857645427 399991564283716700786468141)
    ·
      refine ⟨149996836606393762794925553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399991564283716700786468141 149996836606393762794925553)
      ·
        refine ⟨112497627454795322096194165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149996836606393762794925553 112497627454795322096194165)
        ·
          refine ⟨10546652573887061446518203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112497627454795322096194165 10546652573887061446518203)
          ·
            refine ⟨15819978860830592169777305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546652573887061446518203 15819978860830592169777305)
            ·
              refine ⟨11864984145622944127332979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15819978860830592169777305 11864984145622944127332979)
              ·
                refine ⟨17797476218434416190999469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864984145622944127332979 17797476218434416190999469)
                ·
                  refine ⟨6674053581912906071624801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17797476218434416190999469 6674053581912906071624801)
                  ·
                    refine ⟨5005540186434679553718601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674053581912906071624801 5005540186434679553718601)
                    ·
                      refine ⟨3754155139826009665288951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005540186434679553718601 3754155139826009665288951)
                      ·
                        rfl

theorem cell23_7311191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_7311191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311191 prefixEnd_7311191 := by exact prefixLift 7311191
  have htrace : WordTrace (prefixWord ++ tailWord_7311191) baseStart_7311191 baseEnd_7311191 := by
    simpa [prefixWord, tailWord_7311191, baseEnd_7311191] using wordTrace_append hprefix tailTrace_7311191
  have hstable : (prefixWord ++ tailWord_7311191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311191).length < 2 ^ (prefixWord ++ tailWord_7311191).sum := by decide
  have hdescent : baseEnd_7311191 < baseStart_7311191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311204 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_7311204 : Nat := 118140960795 + 7311204 * 2 ^ 59
def prefixEnd_7311204 : Nat := 4983230072969 + 3 ^ 40 * 7311204 * 2
def baseEnd_7311204 : Nat := 3754161815074518114426391

theorem tailTrace_7311204 : CollatzResearch.WordTrace tailWord_7311204 prefixEnd_7311204 3754161815074518114426391 := by
  unfold tailWord_7311204
  simp only [CollatzResearch.WordTrace]
  refine ⟨133330758502382018538934333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177774344669842691385245777 133330758502382018538934333)
  ·
    refine ⟨49999034438393256952100375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133330758502382018538934333 49999034438393256952100375)
    ·
      refine ⟨74998551657589885428150563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49999034438393256952100375 74998551657589885428150563)
      ·
        refine ⟨112497827486384828142225845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74998551657589885428150563 112497827486384828142225845)
        ·
          refine ⟨10546671326848577638333673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112497827486384828142225845 10546671326848577638333673)
          ·
            refine ⟨7910003495136433228750255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546671326848577638333673 7910003495136433228750255)
            ·
              refine ⟨11865005242704649843125383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910003495136433228750255 11865005242704649843125383)
              ·
                refine ⟨17797507864056974764688075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11865005242704649843125383 17797507864056974764688075)
                ·
                  refine ⟨26696261796085462147032113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17797507864056974764688075 26696261796085462147032113)
                  ·
                    refine ⟨20022196347064096610274085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26696261796085462147032113 20022196347064096610274085)
                    ·
                      refine ⟨3754161815074518114426391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20022196347064096610274085 3754161815074518114426391)
                      ·
                        rfl

theorem cell23_7311204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_7311204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311204 prefixEnd_7311204 := by exact prefixLift 7311204
  have htrace : WordTrace (prefixWord ++ tailWord_7311204) baseStart_7311204 baseEnd_7311204 := by
    simpa [prefixWord, tailWord_7311204, baseEnd_7311204] using wordTrace_append hprefix tailTrace_7311204
  have hstable : (prefixWord ++ tailWord_7311204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311204).length < 2 ^ (prefixWord ++ tailWord_7311204).sum := by decide
  have hdescent : baseEnd_7311204 < baseStart_7311204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311214 : List Nat := [4, 1, 2, 3, 1, 3, 2, 7]
def baseStart_7311214 : Nat := 118140960795 + 7311214 * 2 ^ 59
def prefixEnd_7311214 : Nat := 4983230072969 + 3 ^ 40 * 7311214 * 2
def baseEnd_7311214 : Nat := 139043220365965299085235

theorem tailTrace_7311214 : CollatzResearch.WordTrace tailWord_7311214 prefixEnd_7311214 139043220365965299085235 := by
  unfold tailWord_7311214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33332735216840976098216587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177774587823151872523821797 33332735216840976098216587)
  ·
    refine ⟨49999102825261464147324881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33332735216840976098216587 49999102825261464147324881)
    ·
      refine ⟨37499327118946098110493661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49999102825261464147324881 37499327118946098110493661)
      ·
        refine ⟨14062247669604786791435123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37499327118946098110493661 14062247669604786791435123)
        ·
          refine ⟨21093371504407180187152685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14062247669604786791435123 21093371504407180187152685)
          ·
            refine ⟨7910014314152692570182257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21093371504407180187152685 7910014314152692570182257)
            ·
              refine ⟨5932510735614519427636693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910014314152692570182257 5932510735614519427636693)
              ·
                refine ⟨139043220365965299085235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5932510735614519427636693 139043220365965299085235)
                ·
                  rfl

theorem cell23_7311214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_7311214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311214 prefixEnd_7311214 := by exact prefixLift 7311214
  have htrace : WordTrace (prefixWord ++ tailWord_7311214) baseStart_7311214 baseEnd_7311214 := by
    simpa [prefixWord, tailWord_7311214, baseEnd_7311214] using wordTrace_append hprefix tailTrace_7311214
  have hstable : (prefixWord ++ tailWord_7311214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311214).length < 2 ^ (prefixWord ++ tailWord_7311214).sum := by decide
  have hdescent : baseEnd_7311214 < baseStart_7311214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
