import V185TrunkScan22Chunk051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_467183 : List Nat := [1, 1, 2, 1, 6, 3, 2, 6]
def baseStart_467183 : Nat := 118140960795 + 467183 * 2 ^ 59
def prefixEnd_467183 : Nat := 4983230072969 + 3 ^ 40 * 467183 * 2
def baseEnd_467183 : Nat := 17769587600707472449183

theorem tailTrace_467183 : CollatzResearch.WordTrace tailWord_467183 prefixEnd_467183 17769587600707472449183 := by
  unfold tailWord_467183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039563866483254349222203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359709244322169566148135 17039563866483254349222203)
  ·
    refine ⟨25559345799724881523833305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039563866483254349222203 25559345799724881523833305)
    ·
      refine ⟨19169509349793661142874979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25559345799724881523833305 19169509349793661142874979)
      ·
        refine ⟨28754264024690491714312469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19169509349793661142874979 28754264024690491714312469)
        ·
          refine ⟨1347856126157366799108397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28754264024690491714312469 1347856126157366799108397)
          ·
            refine ⟨505446047309012549665649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1347856126157366799108397 505446047309012549665649)
            ·
              refine ⟨379084535481759412249237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505446047309012549665649 379084535481759412249237)
              ·
                refine ⟨17769587600707472449183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379084535481759412249237 17769587600707472449183)
                ·
                  rfl

theorem cell22_467183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 6].length) (baseStart_467183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467183 prefixEnd_467183 := by exact prefixLift 467183
  have htrace : WordTrace (prefixWord ++ tailWord_467183) baseStart_467183 baseEnd_467183 := by
    simpa [prefixWord, tailWord_467183, baseEnd_467183] using wordTrace_append hprefix tailTrace_467183
  have hstable : (prefixWord ++ tailWord_467183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467183).length < 2 ^ (prefixWord ++ tailWord_467183).sum := by decide
  have hdescent : baseEnd_467183 < baseStart_467183 := by decide
  rcases family_descends (prefixWord ++ tailWord_467183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467211 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 5]
def baseStart_467211 : Nat := 118140960795 + 467211 * 2 ^ 59
def prefixEnd_467211 : Nat := 4983230072969 + 3 ^ 40 * 467211 * 2
def baseEnd_467211 : Nat := 53311957792861504114187

theorem tailTrace_467211 : CollatzResearch.WordTrace tailWord_467211 prefixEnd_467211 53311957792861504114187 := by
  unfold tailWord_467211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17040585110381815131241487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11360390073587876754160991 17040585110381815131241487)
  ·
    refine ⟨25560877665572722696862231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17040585110381815131241487 25560877665572722696862231)
    ·
      refine ⟨38341316498359084045293347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25560877665572722696862231 38341316498359084045293347)
      ·
        refine ⟨57511974747538626067940021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38341316498359084045293347 57511974747538626067940021)
        ·
          refine ⟨5391747632581746193869377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57511974747538626067940021 5391747632581746193869377)
          ·
            refine ⟨4043810724436309645402033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391747632581746193869377 4043810724436309645402033)
            ·
              refine ⟨3032858043327232234051525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043810724436309645402033 3032858043327232234051525)
              ·
                refine ⟨568660883123856043884661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3032858043327232234051525 568660883123856043884661)
                ·
                  refine ⟨53311957792861504114187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568660883123856043884661 53311957792861504114187)
                  ·
                    rfl

theorem cell22_467211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].length) (baseStart_467211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467211 prefixEnd_467211 := by exact prefixLift 467211
  have htrace : WordTrace (prefixWord ++ tailWord_467211) baseStart_467211 baseEnd_467211 := by
    simpa [prefixWord, tailWord_467211, baseEnd_467211] using wordTrace_append hprefix tailTrace_467211
  have hstable : (prefixWord ++ tailWord_467211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467211).length < 2 ^ (prefixWord ++ tailWord_467211).sum := by decide
  have hdescent : baseEnd_467211 < baseStart_467211 := by decide
  rcases family_descends (prefixWord ++ tailWord_467211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467271 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_467271 : Nat := 118140960795 + 467271 * 2 ^ 59
def prefixEnd_467271 : Nat := 4983230072969 + 3 ^ 40 * 467271 * 2
def baseEnd_467271 : Nat := 159956412604764355842377

theorem tailTrace_467271 : CollatzResearch.WordTrace tailWord_467271 prefixEnd_467271 159956412604764355842377 := by
  unfold tailWord_467271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042773490164445378425667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11361848993442963585617111 17042773490164445378425667)
  ·
    refine ⟨25564160235246668067638501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17042773490164445378425667 25564160235246668067638501)
    ·
      refine ⟨4793280044108750262682219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25564160235246668067638501 4793280044108750262682219)
      ·
        refine ⟨7189920066163125394023329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793280044108750262682219 7189920066163125394023329)
        ·
          refine ⟨5392440049622344045517497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189920066163125394023329 5392440049622344045517497)
          ·
            refine ⟨4044330037216758034138123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392440049622344045517497 4044330037216758034138123)
            ·
              refine ⟨6066495055825137051207185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044330037216758034138123 6066495055825137051207185)
              ·
                refine ⟨4549871291868852788405389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066495055825137051207185 4549871291868852788405389)
                ·
                  refine ⟨1706201734450819795652021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549871291868852788405389 1706201734450819795652021)
                  ·
                    refine ⟨159956412604764355842377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1706201734450819795652021 159956412604764355842377)
                    ·
                      rfl

theorem cell22_467271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_467271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467271 prefixEnd_467271 := by exact prefixLift 467271
  have htrace : WordTrace (prefixWord ++ tailWord_467271) baseStart_467271 baseEnd_467271 := by
    simpa [prefixWord, tailWord_467271, baseEnd_467271] using wordTrace_append hprefix tailTrace_467271
  have hstable : (prefixWord ++ tailWord_467271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467271).length < 2 ^ (prefixWord ++ tailWord_467271).sum := by decide
  have hdescent : baseEnd_467271 < baseStart_467271 := by decide
  rcases family_descends (prefixWord ++ tailWord_467271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467303 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_467303 : Nat := 118140960795 + 467303 * 2 ^ 59
def prefixEnd_467303 : Nat := 4983230072969 + 3 ^ 40 * 467303 * 2
def baseEnd_467303 : Nat := 159967366858726939042279

theorem tailTrace_467303 : CollatzResearch.WordTrace tailWord_467303 prefixEnd_467303 159967366858726939042279 := by
  unfold tailWord_467303
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043940626048514843590563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362627084032343229060375 17043940626048514843590563)
  ·
    refine ⟨25565910939072772265385845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17043940626048514843590563 25565910939072772265385845)
    ·
      refine ⟨2396804150538072399879923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25565910939072772265385845 2396804150538072399879923)
      ·
        refine ⟨3595206225807108599819885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396804150538072399879923 3595206225807108599819885)
        ·
          refine ⟨1348202334677665724932457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3595206225807108599819885 1348202334677665724932457)
          ·
            refine ⟨1011151751008249293699343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348202334677665724932457 1011151751008249293699343)
            ·
              refine ⟨1516727626512373940549015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011151751008249293699343 1516727626512373940549015)
              ·
                refine ⟨2275091439768560910823523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516727626512373940549015 2275091439768560910823523)
                ·
                  refine ⟨3412637159652841366235285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275091439768560910823523 3412637159652841366235285)
                  ·
                    refine ⟨159967366858726939042279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3412637159652841366235285 159967366858726939042279)
                    ·
                      rfl

theorem cell22_467303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_467303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467303 prefixEnd_467303 := by exact prefixLift 467303
  have htrace : WordTrace (prefixWord ++ tailWord_467303) baseStart_467303 baseEnd_467303 := by
    simpa [prefixWord, tailWord_467303, baseEnd_467303] using wordTrace_append hprefix tailTrace_467303
  have hstable : (prefixWord ++ tailWord_467303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467303).length < 2 ^ (prefixWord ++ tailWord_467303).sum := by decide
  have hdescent : baseEnd_467303 < baseStart_467303 := by decide
  rcases family_descends (prefixWord ++ tailWord_467303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467376 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_467376 : Nat := 118140960795 + 467376 * 2 ^ 59
def prefixEnd_467376 : Nat := 4983230072969 + 3 ^ 40 * 467376 * 2
def baseEnd_467376 : Nat := 159992356250579081967055

theorem tailTrace_467376 : CollatzResearch.WordTrace tailWord_467376 prefixEnd_467376 159992356250579081967055 := by
  unfold tailWord_467376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8523301577392024155498991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11364402103189365540665321 8523301577392024155498991)
  ·
    refine ⟨12784952366088036233248487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8523301577392024155498991 12784952366088036233248487)
    ·
      refine ⟨19177428549132054349872731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784952366088036233248487 19177428549132054349872731)
      ·
        refine ⟨28766142823698081524809097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19177428549132054349872731 28766142823698081524809097)
        ·
          refine ⟨21574607117773561143606823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28766142823698081524809097 21574607117773561143606823)
          ·
            refine ⟨32361910676660341715410235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574607117773561143606823 32361910676660341715410235)
            ·
              refine ⟨48542866014990512573115353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32361910676660341715410235 48542866014990512573115353)
              ·
                refine ⟨36407149511242884429836515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48542866014990512573115353 36407149511242884429836515)
                ·
                  refine ⟨54610724266864326644754773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36407149511242884429836515 54610724266864326644754773)
                  ·
                    refine ⟨159992356250579081967055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 54610724266864326644754773 159992356250579081967055)
                    ·
                      rfl

theorem cell22_467376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_467376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467376 prefixEnd_467376 := by exact prefixLift 467376
  have htrace : WordTrace (prefixWord ++ tailWord_467376) baseStart_467376 baseEnd_467376 := by
    simpa [prefixWord, tailWord_467376, baseEnd_467376] using wordTrace_append hprefix tailTrace_467376
  have hstable : (prefixWord ++ tailWord_467376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467376).length < 2 ^ (prefixWord ++ tailWord_467376).sum := by decide
  have hdescent : baseEnd_467376 < baseStart_467376 := by decide
  rcases family_descends (prefixWord ++ tailWord_467376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467423 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_467423 : Nat := 118140960795 + 467423 * 2 ^ 59
def prefixEnd_467423 : Nat := 4983230072969 + 3 ^ 40 * 467423 * 2
def baseEnd_467423 : Nat := 160008445311086626041911

theorem tailTrace_467423 : CollatzResearch.WordTrace tailWord_467423 prefixEnd_467423 160008445311086626041911 := by
  unfold tailWord_467423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048317385613775337958923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11365544923742516891972615 17048317385613775337958923)
  ·
    refine ⟨25572476078420663006938385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17048317385613775337958923 25572476078420663006938385)
    ·
      refine ⟨19179357058815497255203789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25572476078420663006938385 19179357058815497255203789)
      ·
        refine ⟨7192258897055811470701421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19179357058815497255203789 7192258897055811470701421)
        ·
          refine ⟨2697097086395929301513033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7192258897055811470701421 2697097086395929301513033)
          ·
            refine ⟨2022822814796946976134775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697097086395929301513033 2022822814796946976134775)
            ·
              refine ⟨3034234222195420464202163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022822814796946976134775 3034234222195420464202163)
              ·
                refine ⟨4551351333293130696303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034234222195420464202163 4551351333293130696303245)
                ·
                  refine ⟨1706756749984924011113717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4551351333293130696303245 1706756749984924011113717)
                  ·
                    refine ⟨160008445311086626041911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1706756749984924011113717 160008445311086626041911)
                    ·
                      rfl

theorem cell22_467423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_467423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467423 prefixEnd_467423 := by exact prefixLift 467423
  have htrace : WordTrace (prefixWord ++ tailWord_467423) baseStart_467423 baseEnd_467423 := by
    simpa [prefixWord, tailWord_467423, baseEnd_467423] using wordTrace_append hprefix tailTrace_467423
  have hstable : (prefixWord ++ tailWord_467423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467423).length < 2 ^ (prefixWord ++ tailWord_467423).sum := by decide
  have hdescent : baseEnd_467423 < baseStart_467423 := by decide
  rcases family_descends (prefixWord ++ tailWord_467423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467425 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 4]
def baseStart_467425 : Nat := 118140960795 + 467425 * 2 ^ 59
def prefixEnd_467425 : Nat := 4983230072969 + 3 ^ 40 * 467425 * 2
def baseEnd_467425 : Nat := 53336376650653095830635

theorem tailTrace_467425 : CollatzResearch.WordTrace tailWord_467425 prefixEnd_467425 53336376650653095830635 := by
  unfold tailWord_467425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048390331606529679531729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11365593554404353119687819 17048390331606529679531729)
  ·
    refine ⟨12786292748704897259648797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17048390331606529679531729 12786292748704897259648797)
    ·
      refine ⟨4794859780764336472368299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12786292748704897259648797 4794859780764336472368299)
      ·
        refine ⟨7192289671146504708552449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794859780764336472368299 7192289671146504708552449)
        ·
          refine ⟨5394217253359878531414337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192289671146504708552449 5394217253359878531414337)
          ·
            refine ⟨4045662940019908898560753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5394217253359878531414337 4045662940019908898560753)
            ·
              refine ⟨3034247205014931673920565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045662940019908898560753 3034247205014931673920565)
              ·
                refine ⟨284460675470149844430053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3034247205014931673920565 284460675470149844430053)
                ·
                  refine ⟨53336376650653095830635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284460675470149844430053 53336376650653095830635)
                  ·
                    rfl

theorem cell22_467425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_467425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467425 prefixEnd_467425 := by exact prefixLift 467425
  have htrace : WordTrace (prefixWord ++ tailWord_467425) baseStart_467425 baseEnd_467425 := by
    simpa [prefixWord, tailWord_467425, baseEnd_467425] using wordTrace_append hprefix tailTrace_467425
  have hstable : (prefixWord ++ tailWord_467425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467425).length < 2 ^ (prefixWord ++ tailWord_467425).sum := by decide
  have hdescent : baseEnd_467425 < baseStart_467425 := by decide
  rcases family_descends (prefixWord ++ tailWord_467425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467457 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_467457 : Nat := 118140960795 + 467457 * 2 ^ 59
def prefixEnd_467457 : Nat := 4983230072969 + 3 ^ 40 * 467457 * 2
def baseEnd_467457 : Nat := 160020084205921870691807

theorem tailTrace_467457 : CollatzResearch.WordTrace tailWord_467457 prefixEnd_467457 160020084205921870691807 := by
  unfold tailWord_467457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049557467490599144696625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11366371644993732763131083 17049557467490599144696625)
  ·
    refine ⟨12787168100617949358522469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17049557467490599144696625 12787168100617949358522469)
    ·
      refine ⟨2397594018865865504722963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12787168100617949358522469 2397594018865865504722963)
      ·
        refine ⟨3596391028298798257084445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397594018865865504722963 3596391028298798257084445)
        ·
          refine ⟨1348646635612049346406667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3596391028298798257084445 1348646635612049346406667)
          ·
            refine ⟨2022969953418074019610001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348646635612049346406667 2022969953418074019610001)
            ·
              refine ⟨1517227465063555514707501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022969953418074019610001 1517227465063555514707501)
              ·
                refine ⟨568960299398833318015313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517227465063555514707501 568960299398833318015313)
                ·
                  refine ⟨426720224549124988511485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568960299398833318015313 426720224549124988511485)
                  ·
                    refine ⟨160020084205921870691807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426720224549124988511485 160020084205921870691807)
                    ·
                      rfl

theorem cell22_467457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_467457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467457 prefixEnd_467457 := by exact prefixLift 467457
  have htrace : WordTrace (prefixWord ++ tailWord_467457) baseStart_467457 baseEnd_467457 := by
    simpa [prefixWord, tailWord_467457, baseEnd_467457] using wordTrace_append hprefix tailTrace_467457
  have hstable : (prefixWord ++ tailWord_467457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467457).length < 2 ^ (prefixWord ++ tailWord_467457).sum := by decide
  have hdescent : baseEnd_467457 < baseStart_467457 := by decide
  rcases family_descends (prefixWord ++ tailWord_467457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467508 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_467508 : Nat := 118140960795 + 467508 * 2 ^ 59
def prefixEnd_467508 : Nat := 4983230072969 + 3 ^ 40 * 467508 * 2
def baseEnd_467508 : Nat := 160037542548174737666651

theorem tailTrace_467508 : CollatzResearch.WordTrace tailWord_467508 prefixEnd_467508 160037542548174737666651 := by
  unfold tailWord_467508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525708795152917427401589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11367611726870556569868785 8525708795152917427401589)
  ·
    refine ⟨799285199545586008818899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8525708795152917427401589 799285199545586008818899)
    ·
      refine ⟨1198927799318379013228349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799285199545586008818899 1198927799318379013228349)
      ·
        refine ⟨449597924744392129960631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198927799318379013228349 449597924744392129960631)
        ·
          refine ⟨674396887116588194940947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449597924744392129960631 674396887116588194940947)
          ·
            refine ⟨1011595330674882292411421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674396887116588194940947 1011595330674882292411421)
            ·
              refine ⟨379348249003080859654283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011595330674882292411421 379348249003080859654283)
              ·
                refine ⟨569022373504621289481425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379348249003080859654283 569022373504621289481425)
                ·
                  refine ⟨426766780128465967111069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569022373504621289481425 426766780128465967111069)
                  ·
                    refine ⟨160037542548174737666651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426766780128465967111069 160037542548174737666651)
                    ·
                      rfl

theorem cell22_467508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_467508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467508 prefixEnd_467508 := by exact prefixLift 467508
  have htrace : WordTrace (prefixWord ++ tailWord_467508) baseStart_467508 baseEnd_467508 := by
    simpa [prefixWord, tailWord_467508, baseEnd_467508] using wordTrace_append hprefix tailTrace_467508
  have hstable : (prefixWord ++ tailWord_467508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467508).length < 2 ^ (prefixWord ++ tailWord_467508).sum := by decide
  have hdescent : baseEnd_467508 < baseStart_467508 := by decide
  rcases family_descends (prefixWord ++ tailWord_467508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467528 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_467528 : Nat := 118140960795 + 467528 * 2 ^ 59
def prefixEnd_467528 : Nat := 4983230072969 + 3 ^ 40 * 467528 * 2
def baseEnd_467528 : Nat := 160044388956901352166589

theorem tailTrace_467528 : CollatzResearch.WordTrace tailWord_467528 prefixEnd_467528 160044388956901352166589 := by
  unfold tailWord_467528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526073525116689135265619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11368098033488918847020825 8526073525116689135265619)
  ·
    refine ⟨12789110287675033702898429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526073525116689135265619 12789110287675033702898429)
    ·
      refine ⟨4795916357878137638586911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12789110287675033702898429 4795916357878137638586911)
      ·
        refine ⟨7193874536817206457880367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795916357878137638586911 7193874536817206457880367)
        ·
          refine ⟨10790811805225809686820551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193874536817206457880367 10790811805225809686820551)
          ·
            refine ⟨16186217707838714530230827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790811805225809686820551 16186217707838714530230827)
            ·
              refine ⟨24279326561758071795346241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186217707838714530230827 24279326561758071795346241)
              ·
                refine ⟨18209494921318553846509681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24279326561758071795346241 18209494921318553846509681)
                ·
                  refine ⟨13657121190988915384882261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18209494921318553846509681 13657121190988915384882261)
                  ·
                    refine ⟨160044388956901352166589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13657121190988915384882261 160044388956901352166589)
                    ·
                      rfl

theorem cell22_467528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_467528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467528 prefixEnd_467528 := by exact prefixLift 467528
  have htrace : WordTrace (prefixWord ++ tailWord_467528) baseStart_467528 baseEnd_467528 := by
    simpa [prefixWord, tailWord_467528, baseEnd_467528] using wordTrace_append hprefix tailTrace_467528
  have hstable : (prefixWord ++ tailWord_467528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467528).length < 2 ^ (prefixWord ++ tailWord_467528).sum := by decide
  have hdescent : baseEnd_467528 < baseStart_467528 := by decide
  rcases family_descends (prefixWord ++ tailWord_467528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467626 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_467626 : Nat := 118140960795 + 467626 * 2 ^ 59
def prefixEnd_467626 : Nat := 4983230072969 + 3 ^ 40 * 467626 * 2
def baseEnd_467626 : Nat := 160077936359661763216289

theorem tailTrace_467626 : CollatzResearch.WordTrace tailWord_467626 prefixEnd_467626 160077936359661763216289 := by
  unfold tailWord_467626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263930350969585251899683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11370480935918894005065821 4263930350969585251899683)
  ·
    refine ⟨6395895526454377877849525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4263930350969585251899683 6395895526454377877849525)
    ·
      refine ⟨599615205605097926048393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6395895526454377877849525 599615205605097926048393)
      ·
        refine ⟨449711404203823444536295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599615205605097926048393 449711404203823444536295)
        ·
          refine ⟨674567106305735166804443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449711404203823444536295 674567106305735166804443)
          ·
            refine ⟨1011850659458602750206665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674567106305735166804443 1011850659458602750206665)
            ·
              refine ⟨758887994593952062654999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011850659458602750206665 758887994593952062654999)
              ·
                refine ⟨1138331991890928093982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758887994593952062654999 1138331991890928093982499)
                ·
                  refine ⟨1707497987836392140973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138331991890928093982499 1707497987836392140973749)
                  ·
                    refine ⟨160077936359661763216289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1707497987836392140973749 160077936359661763216289)
                    ·
                      rfl

theorem cell22_467626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_467626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467626 prefixEnd_467626 := by exact prefixLift 467626
  have htrace : WordTrace (prefixWord ++ tailWord_467626) baseStart_467626 baseEnd_467626 := by
    simpa [prefixWord, tailWord_467626, baseEnd_467626] using wordTrace_append hprefix tailTrace_467626
  have hstable : (prefixWord ++ tailWord_467626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467626).length < 2 ^ (prefixWord ++ tailWord_467626).sum := by decide
  have hdescent : baseEnd_467626 < baseStart_467626 := by decide
  rcases family_descends (prefixWord ++ tailWord_467626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467665 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_467665 : Nat := 118140960795 + 467665 * 2 ^ 59
def prefixEnd_467665 : Nat := 4983230072969 + 3 ^ 40 * 467665 * 2
def baseEnd_467665 : Nat := 160091286856678661491169

theorem tailTrace_467665 : CollatzResearch.WordTrace tailWord_467665 prefixEnd_467665 160091286856678661491169 := by
  unfold tailWord_467665
  simp only [CollatzResearch.WordTrace]
  refine ⟨17057143850737050668268449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11371429233824700445512299 17057143850737050668268449)
  ·
    refine ⟨12792857888052788001201337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17057143850737050668268449 12792857888052788001201337)
    ·
      refine ⟨9594643416039591000901003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12792857888052788001201337 9594643416039591000901003)
      ·
        refine ⟨14391965124059386501351505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594643416039591000901003 14391965124059386501351505)
        ·
          refine ⟨10793973843044539876013629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14391965124059386501351505 10793973843044539876013629)
          ·
            refine ⟨4047740191141702453505111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10793973843044539876013629 4047740191141702453505111)
            ·
              refine ⟨6071610286712553680257667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047740191141702453505111 6071610286712553680257667)
              ·
                refine ⟨9107415430068830520386501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071610286712553680257667 9107415430068830520386501)
                ·
                  refine ⟨1707640393137905722572469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9107415430068830520386501 1707640393137905722572469)
                  ·
                    refine ⟨160091286856678661491169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1707640393137905722572469 160091286856678661491169)
                    ·
                      rfl

theorem cell22_467665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_467665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467665 prefixEnd_467665 := by exact prefixLift 467665
  have htrace : WordTrace (prefixWord ++ tailWord_467665) baseStart_467665 baseEnd_467665 := by
    simpa [prefixWord, tailWord_467665, baseEnd_467665] using wordTrace_append hprefix tailTrace_467665
  have hstable : (prefixWord ++ tailWord_467665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467665).length < 2 ^ (prefixWord ++ tailWord_467665).sum := by decide
  have hdescent : baseEnd_467665 < baseStart_467665 := by decide
  rcases family_descends (prefixWord ++ tailWord_467665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467684 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_467684 : Nat := 118140960795 + 467684 * 2 ^ 59
def prefixEnd_467684 : Nat := 4983230072969 + 3 ^ 40 * 467684 * 2
def baseEnd_467684 : Nat := 53365930314989648422037

theorem tailTrace_467684 : CollatzResearch.WordTrace tailWord_467684 prefixEnd_467684 53365930314989648422037 := by
  unfold tailWord_467684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528918418834108456605053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11371891225112144608806737 8528918418834108456605053)
  ·
    refine ⟨3198344407062790671226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8528918418834108456605053 3198344407062790671226895)
    ·
      refine ⟨4797516610594186006840343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198344407062790671226895 4797516610594186006840343)
      ·
        refine ⟨7196274915891279010260515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797516610594186006840343 7196274915891279010260515)
        ·
          refine ⟨10794412373836918515390773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196274915891279010260515 10794412373836918515390773)
          ·
            refine ⟨1011976160047211110817885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10794412373836918515390773 1011976160047211110817885)
            ·
              refine ⟨379491060017704166556707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011976160047211110817885 379491060017704166556707)
              ·
                refine ⟨569236590026556249835061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379491060017704166556707 569236590026556249835061)
                ·
                  refine ⟨53365930314989648422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569236590026556249835061 53365930314989648422037)
                  ·
                    rfl

theorem cell22_467684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_467684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467684 prefixEnd_467684 := by exact prefixLift 467684
  have htrace : WordTrace (prefixWord ++ tailWord_467684) baseStart_467684 baseEnd_467684 := by
    simpa [prefixWord, tailWord_467684, baseEnd_467684] using wordTrace_append hprefix tailTrace_467684
  have hstable : (prefixWord ++ tailWord_467684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467684).length < 2 ^ (prefixWord ++ tailWord_467684).sum := by decide
  have hdescent : baseEnd_467684 < baseStart_467684 := by decide
  rcases family_descends (prefixWord ++ tailWord_467684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467727 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 4, 3]
def baseStart_467727 : Nat := 118140960795 + 467727 * 2 ^ 59
def prefixEnd_467727 : Nat := 4983230072969 + 3 ^ 40 * 467727 * 2
def baseEnd_467727 : Nat := 160112510723731166440979

theorem tailTrace_467727 : CollatzResearch.WordTrace tailWord_467727 prefixEnd_467727 160112510723731166440979 := by
  unfold tailWord_467727
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059405176512435257025435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11372936784341623504683623 17059405176512435257025435)
  ·
    refine ⟨25589107764768652885538153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059405176512435257025435 25589107764768652885538153)
    ·
      refine ⟨19191830823576489664153615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589107764768652885538153 19191830823576489664153615)
      ·
        refine ⟨28787746235364734496230423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191830823576489664153615 28787746235364734496230423)
        ·
          refine ⟨43181619353047101744345635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28787746235364734496230423 43181619353047101744345635)
          ·
            refine ⟨64772429029570652616518453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43181619353047101744345635 64772429029570652616518453)
            ·
              refine ⟨6072415221522248682798605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64772429029570652616518453 6072415221522248682798605)
              ·
                refine ⟨2277155708070843256049477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072415221522248682798605 2277155708070843256049477)
                ·
                  refine ⟨426966695263283110509277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277155708070843256049477 426966695263283110509277)
                  ·
                    refine ⟨160112510723731166440979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426966695263283110509277 160112510723731166440979)
                    ·
                      rfl

theorem cell22_467727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_467727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467727 prefixEnd_467727 := by exact prefixLift 467727
  have htrace : WordTrace (prefixWord ++ tailWord_467727) baseStart_467727 baseEnd_467727 := by
    simpa [prefixWord, tailWord_467727, baseEnd_467727] using wordTrace_append hprefix tailTrace_467727
  have hstable : (prefixWord ++ tailWord_467727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467727).length < 2 ^ (prefixWord ++ tailWord_467727).sum := by decide
  have hdescent : baseEnd_467727 < baseStart_467727 := by decide
  rcases family_descends (prefixWord ++ tailWord_467727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467748 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_467748 : Nat := 118140960795 + 467748 * 2 ^ 59
def prefixEnd_467748 : Nat := 4983230072969 + 3 ^ 40 * 467748 * 2
def baseEnd_467748 : Nat := 160119699452894111665915

theorem tailTrace_467748 : CollatzResearch.WordTrace tailWord_467748 prefixEnd_467748 160119699452894111665915 := by
  unfold tailWord_467748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8530085554718177921769949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11373447406290903895693265 8530085554718177921769949)
  ·
    refine ⟨3198782083019316720663731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8530085554718177921769949 3198782083019316720663731)
    ·
      refine ⟨4798173124528975080995597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198782083019316720663731 4798173124528975080995597)
      ·
        refine ⟨1799314921698365655373349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4798173124528975080995597 1799314921698365655373349)
        ·
          refine ⟨337371547818443560382503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1799314921698365655373349 337371547818443560382503)
          ·
            refine ⟨506057321727665340573755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337371547818443560382503 506057321727665340573755)
            ·
              refine ⟨759085982591498010860633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506057321727665340573755 759085982591498010860633)
              ·
                refine ⟨569314486943623508145475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759085982591498010860633 569314486943623508145475)
                ·
                  refine ⟨853971730415435262218213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569314486943623508145475 853971730415435262218213)
                  ·
                    refine ⟨160119699452894111665915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 853971730415435262218213 160119699452894111665915)
                    ·
                      rfl

theorem cell22_467748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_467748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467748 prefixEnd_467748 := by exact prefixLift 467748
  have htrace : WordTrace (prefixWord ++ tailWord_467748) baseStart_467748 baseEnd_467748 := by
    simpa [prefixWord, tailWord_467748, baseEnd_467748] using wordTrace_append hprefix tailTrace_467748
  have hstable : (prefixWord ++ tailWord_467748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467748).length < 2 ^ (prefixWord ++ tailWord_467748).sum := by decide
  have hdescent : baseEnd_467748 < baseStart_467748 := by decide
  rcases family_descends (prefixWord ++ tailWord_467748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_467755 : Nat := 118140960795 + 467755 * 2 ^ 59
def prefixEnd_467755 : Nat := 4983230072969 + 3 ^ 40 * 467755 * 2
def baseEnd_467755 : Nat := 160122095695948426740893

theorem tailTrace_467755 : CollatzResearch.WordTrace tailWord_467755 prefixEnd_467755 160122095695948426740893 := by
  unfold tailWord_467755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060426420410996039044719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11373617613607330692696479 17060426420410996039044719)
  ·
    refine ⟨25590639630616494058567079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17060426420410996039044719 25590639630616494058567079)
    ·
      refine ⟨38385959445924741087850619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25590639630616494058567079 38385959445924741087850619)
      ·
        refine ⟨57578939168887111631775929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38385959445924741087850619 57578939168887111631775929)
        ·
          refine ⟨43184204376665333723831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57578939168887111631775929 43184204376665333723831947)
          ·
            refine ⟨64776306564998000585747921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43184204376665333723831947 64776306564998000585747921)
            ·
              refine ⟨48582229923748500439310941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64776306564998000585747921 48582229923748500439310941)
              ·
                refine ⟨18218336221405687664741603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48582229923748500439310941 18218336221405687664741603)
                ·
                  refine ⟨27327504332108531497112405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18218336221405687664741603 27327504332108531497112405)
                  ·
                    refine ⟨160122095695948426740893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27327504332108531497112405 160122095695948426740893)
                    ·
                      rfl

theorem cell22_467755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_467755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467755 prefixEnd_467755 := by exact prefixLift 467755
  have htrace : WordTrace (prefixWord ++ tailWord_467755) baseStart_467755 baseEnd_467755 := by
    simpa [prefixWord, tailWord_467755, baseEnd_467755] using wordTrace_append hprefix tailTrace_467755
  have hstable : (prefixWord ++ tailWord_467755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467755).length < 2 ^ (prefixWord ++ tailWord_467755).sum := by decide
  have hdescent : baseEnd_467755 < baseStart_467755 := by decide
  rcases family_descends (prefixWord ++ tailWord_467755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467774 : List Nat := [4, 2, 1, 2, 4, 9]
def baseStart_467774 : Nat := 118140960795 + 467774 * 2 ^ 59
def prefixEnd_467774 : Nat := 4983230072969 + 3 ^ 40 * 467774 * 2
def baseEnd_467774 : Nat := 1976896293632576673035

theorem tailTrace_467774 : CollatzResearch.WordTrace tailWord_467774 prefixEnd_467774 1976896293632576673035 := by
  unfold tailWord_467774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132639925917770285498297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11374079604894774855990917 2132639925917770285498297)
  ·
    refine ⟨1599479944438327714123723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2132639925917770285498297 1599479944438327714123723)
    ·
      refine ⟨2399219916657491571185585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599479944438327714123723 2399219916657491571185585)
      ·
        refine ⟨1799414937493118678389189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2399219916657491571185585 1799414937493118678389189)
        ·
          refine ⟨337390300779959752197973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1799414937493118678389189 337390300779959752197973)
          ·
            refine ⟨1976896293632576673035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 337390300779959752197973 1976896293632576673035)
            ·
              rfl

theorem cell22_467774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 9].length) (baseStart_467774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467774 prefixEnd_467774 := by exact prefixLift 467774
  have htrace : WordTrace (prefixWord ++ tailWord_467774) baseStart_467774 baseEnd_467774 := by
    simpa [prefixWord, tailWord_467774, baseEnd_467774] using wordTrace_append hprefix tailTrace_467774
  have hstable : (prefixWord ++ tailWord_467774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467774).length < 2 ^ (prefixWord ++ tailWord_467774).sum := by decide
  have hdescent : baseEnd_467774 < baseStart_467774 := by decide
  rcases family_descends (prefixWord ++ tailWord_467774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_467832 : Nat := 118140960795 + 467832 * 2 ^ 59
def prefixEnd_467832 : Nat := 4983230072969 + 3 ^ 40 * 467832 * 2
def baseEnd_467832 : Nat := 160148454369545892565657

theorem tailTrace_467832 : CollatzResearch.WordTrace tailWord_467832 prefixEnd_467832 160148454369545892565657 := by
  unfold tailWord_467832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531617420566019094798875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11375489894088025459731833 8531617420566019094798875)
  ·
    refine ⟨12797426130849028642198313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8531617420566019094798875 12797426130849028642198313)
    ·
      refine ⟨9598069598136771481648735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12797426130849028642198313 9598069598136771481648735)
      ·
        refine ⟨14397104397205157222473103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598069598136771481648735 14397104397205157222473103)
        ·
          refine ⟨21595656595807735833709655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397104397205157222473103 21595656595807735833709655)
          ·
            refine ⟨32393484893711603750564483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21595656595807735833709655 32393484893711603750564483)
            ·
              refine ⟨48590227340567405625846725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32393484893711603750564483 48590227340567405625846725)
              ·
                refine ⟨9110667626356388554846261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48590227340567405625846725 9110667626356388554846261)
                ·
                  refine ⟨854125089970911427016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9110667626356388554846261 854125089970911427016837)
                  ·
                    refine ⟨160148454369545892565657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 854125089970911427016837 160148454369545892565657)
                    ·
                      rfl

theorem cell22_467832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_467832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467832 prefixEnd_467832 := by exact prefixLift 467832
  have htrace : WordTrace (prefixWord ++ tailWord_467832) baseStart_467832 baseEnd_467832 := by
    simpa [prefixWord, tailWord_467832, baseEnd_467832] using wordTrace_append hprefix tailTrace_467832
  have hstable : (prefixWord ++ tailWord_467832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467832).length < 2 ^ (prefixWord ++ tailWord_467832).sum := by decide
  have hdescent : baseEnd_467832 < baseStart_467832 := by decide
  rcases family_descends (prefixWord ++ tailWord_467832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467926 : List Nat := [5, 2, 1, 1, 2, 1, 2, 8]
def baseStart_467926 : Nat := 118140960795 + 467926 * 2 ^ 59
def prefixEnd_467926 : Nat := 4983230072969 + 3 ^ 40 * 467926 * 2
def baseEnd_467926 : Nat := 17797848054506775635041

theorem tailTrace_467926 : CollatzResearch.WordTrace tailWord_467926 prefixEnd_467926 17797848054506775635041 := by
  unfold tailWord_467926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066666456424468265219977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11377775535194328162346421 1066666456424468265219977)
  ·
    refine ⟨799999842318351198914983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1066666456424468265219977 799999842318351198914983)
    ·
      refine ⟨1199999763477526798372475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799999842318351198914983 1199999763477526798372475)
      ·
        refine ⟨1799999645216290197558713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199999763477526798372475 1799999645216290197558713)
        ·
          refine ⟨1349999733912217648169035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799999645216290197558713 1349999733912217648169035)
          ·
            refine ⟨2024999600868326472253553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349999733912217648169035 2024999600868326472253553)
            ·
              refine ⟨1518749700651244854190165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024999600868326472253553 1518749700651244854190165)
              ·
                refine ⟨17797848054506775635041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1518749700651244854190165 17797848054506775635041)
                ·
                  rfl

theorem cell22_467926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_467926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467926 prefixEnd_467926 := by exact prefixLift 467926
  have htrace : WordTrace (prefixWord ++ tailWord_467926) baseStart_467926 baseEnd_467926 := by
    simpa [prefixWord, tailWord_467926, baseEnd_467926] using wordTrace_append hprefix tailTrace_467926
  have hstable : (prefixWord ++ tailWord_467926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467926).length < 2 ^ (prefixWord ++ tailWord_467926).sum := by decide
  have hdescent : baseEnd_467926 < baseStart_467926 := by decide
  rcases family_descends (prefixWord ++ tailWord_467926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467969 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_467969 : Nat := 118140960795 + 467969 * 2 ^ 59
def prefixEnd_467969 : Nat := 4983230072969 + 3 ^ 40 * 467969 * 2
def baseEnd_467969 : Nat := 160195352269323201890237

theorem tailTrace_467969 : CollatzResearch.WordTrace tailWord_467969 prefixEnd_467969 160195352269323201890237 := by
  unfold tailWord_467969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068231641635710587334961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11378821094423807058223307 17068231641635710587334961)
  ·
    refine ⟨12801173731226782940501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17068231641635710587334961 12801173731226782940501221)
    ·
      refine ⟨2400220074605021801343979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12801173731226782940501221 2400220074605021801343979)
      ·
        refine ⟨3600330111907532702015969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400220074605021801343979 3600330111907532702015969)
        ·
          refine ⟨2700247583930649526511977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600330111907532702015969 2700247583930649526511977)
          ·
            refine ⟨2025185687947987144883983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2700247583930649526511977 2025185687947987144883983)
            ·
              refine ⟨3037778531921980717325975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025185687947987144883983 3037778531921980717325975)
              ·
                refine ⟨4556667797882971075988963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037778531921980717325975 4556667797882971075988963)
                ·
                  refine ⟨6835001696824456613983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556667797882971075988963 6835001696824456613983445)
                  ·
                    refine ⟨160195352269323201890237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6835001696824456613983445 160195352269323201890237)
                    ·
                      rfl

theorem cell22_467969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_467969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467969 prefixEnd_467969 := by exact prefixLift 467969
  have htrace : WordTrace (prefixWord ++ tailWord_467969) baseStart_467969 baseEnd_467969 := by
    simpa [prefixWord, tailWord_467969, baseEnd_467969] using wordTrace_append hprefix tailTrace_467969
  have hstable : (prefixWord ++ tailWord_467969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467969).length < 2 ^ (prefixWord ++ tailWord_467969).sum := by decide
  have hdescent : baseEnd_467969 < baseStart_467969 := by decide
  rcases family_descends (prefixWord ++ tailWord_467969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468016 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_468016 : Nat := 118140960795 + 468016 * 2 ^ 59
def prefixEnd_468016 : Nat := 4983230072969 + 3 ^ 40 * 468016 * 2
def baseEnd_468016 : Nat := 53403813776610248655031

theorem tailTrace_468016 : CollatzResearch.WordTrace tailWord_468016 prefixEnd_468016 53403813776610248655031 := by
  unfold tailWord_468016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534972936232718807147951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11379963914976958409530601 8534972936232718807147951)
  ·
    refine ⟨12802459404349078210721927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8534972936232718807147951 12802459404349078210721927)
    ·
      refine ⟨19203689106523617316082891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802459404349078210721927 19203689106523617316082891)
      ·
        refine ⟨28805533659785425974124337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19203689106523617316082891 28805533659785425974124337)
        ·
          refine ⟨21604150244839069480593253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28805533659785425974124337 21604150244839069480593253)
          ·
            refine ⟨4050778170907325527611235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21604150244839069480593253 4050778170907325527611235)
            ·
              refine ⟨6076167256360988291416853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050778170907325527611235 6076167256360988291416853)
              ·
                refine ⟨284820340141921326160165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6076167256360988291416853 284820340141921326160165)
                ·
                  refine ⟨53403813776610248655031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284820340141921326160165 53403813776610248655031)
                  ·
                    rfl

theorem cell22_468016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_468016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468016 prefixEnd_468016 := by exact prefixLift 468016
  have htrace : WordTrace (prefixWord ++ tailWord_468016) baseStart_468016 baseEnd_468016 := by
    simpa [prefixWord, tailWord_468016, baseEnd_468016] using wordTrace_append hprefix tailTrace_468016
  have hstable : (prefixWord ++ tailWord_468016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468016).length < 2 ^ (prefixWord ++ tailWord_468016).sum := by decide
  have hdescent : baseEnd_468016 < baseStart_468016 := by decide
  rcases family_descends (prefixWord ++ tailWord_468016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468046 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_468046 : Nat := 118140960795 + 468046 * 2 ^ 59
def prefixEnd_468046 : Nat := 4983230072969 + 3 ^ 40 * 468046 * 2
def baseEnd_468046 : Nat := 160221710942920667715001

theorem tailTrace_468046 : CollatzResearch.WordTrace tailWord_468046 prefixEnd_468046 160221710942920667715001 := by
  unfold tailWord_468046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133880007794594092235999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11380693374904501825258661 2133880007794594092235999)
  ·
    refine ⟨3200820011691891138353999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133880007794594092235999 3200820011691891138353999)
    ·
      refine ⟨4801230017537836707530999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200820011691891138353999 4801230017537836707530999)
      ·
        refine ⟨7201845026306755061296499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801230017537836707530999 7201845026306755061296499)
        ·
          refine ⟨10802767539460132591944749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201845026306755061296499 10802767539460132591944749)
          ·
            refine ⟨4051037827297549721979281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10802767539460132591944749 4051037827297549721979281)
            ·
              refine ⟨3038278370473162291484461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4051037827297549721979281 3038278370473162291484461)
              ·
                refine ⟨1139354388927435859306673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3038278370473162291484461 1139354388927435859306673)
                ·
                  refine ⟨854515791695576894480005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139354388927435859306673 854515791695576894480005)
                  ·
                    refine ⟨160221710942920667715001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 854515791695576894480005 160221710942920667715001)
                    ·
                      rfl

theorem cell22_468046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_468046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468046 prefixEnd_468046 := by exact prefixLift 468046
  have htrace : WordTrace (prefixWord ++ tailWord_468046) baseStart_468046 baseEnd_468046 := by
    simpa [prefixWord, tailWord_468046, baseEnd_468046] using wordTrace_append hprefix tailTrace_468046
  have hstable : (prefixWord ++ tailWord_468046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468046).length < 2 ^ (prefixWord ++ tailWord_468046).sum := by decide
  have hdescent : baseEnd_468046 < baseStart_468046 := by decide
  rcases family_descends (prefixWord ++ tailWord_468046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468050 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_468050 : Nat := 118140960795 + 468050 * 2 ^ 59
def prefixEnd_468050 : Nat := 4983230072969 + 3 ^ 40 * 468050 * 2
def baseEnd_468050 : Nat := 53407693408221996871663

theorem tailTrace_468050 : CollatzResearch.WordTrace tailWord_468050 prefixEnd_468050 53407693408221996871663 := by
  unfold tailWord_468050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267796488585565355258401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11380790636228174280689069 4267796488585565355258401)
  ·
    refine ⟨3200847366439174016443801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4267796488585565355258401 3200847366439174016443801)
    ·
      refine ⟨2400635524829380512332851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3200847366439174016443801 2400635524829380512332851)
      ·
        refine ⟨3600953287244070768499277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400635524829380512332851 3600953287244070768499277)
        ·
          refine ⟨1350357482716526538187229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3600953287244070768499277 1350357482716526538187229)
          ·
            refine ⟨506384056018697451820211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1350357482716526538187229 506384056018697451820211)
            ·
              refine ⟨759576084028046177730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506384056018697451820211 759576084028046177730317)
              ·
                refine ⟨284841031510517316648869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759576084028046177730317 284841031510517316648869)
                ·
                  refine ⟨53407693408221996871663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284841031510517316648869 53407693408221996871663)
                  ·
                    rfl

theorem cell22_468050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_468050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468050 prefixEnd_468050 := by exact prefixLift 468050
  have htrace : WordTrace (prefixWord ++ tailWord_468050) baseStart_468050 baseEnd_468050 := by
    simpa [prefixWord, tailWord_468050, baseEnd_468050] using wordTrace_append hprefix tailTrace_468050
  have hstable : (prefixWord ++ tailWord_468050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468050).length < 2 ^ (prefixWord ++ tailWord_468050).sum := by decide
  have hdescent : baseEnd_468050 < baseStart_468050 := by decide
  rcases family_descends (prefixWord ++ tailWord_468050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468127 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 1, 3]
def baseStart_468127 : Nat := 118140960795 + 468127 * 2 ^ 59
def prefixEnd_468127 : Nat := 4983230072969 + 3 ^ 40 * 468127 * 2
def baseEnd_468127 : Nat := 160249438898263456439753

theorem tailTrace_468127 : CollatzResearch.WordTrace tailWord_468127 prefixEnd_468127 160249438898263456439753 := by
  unfold tailWord_468127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073994375063303571586635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11382662916708869047724423 17073994375063303571586635)
  ·
    refine ⟨25610991562594955357379953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073994375063303571586635 25610991562594955357379953)
    ·
      refine ⟨19208243671946216518034965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25610991562594955357379953 19208243671946216518034965)
      ·
        refine ⟨900386422122478899282889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19208243671946216518034965 900386422122478899282889)
        ·
          refine ⟨675289816591859174462167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900386422122478899282889 675289816591859174462167)
          ·
            refine ⟨1012934724887788761693251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675289816591859174462167 1012934724887788761693251)
            ·
              refine ⟨1519402087331683142539877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012934724887788761693251 1519402087331683142539877)
              ·
                refine ⟨284887891374690589226227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1519402087331683142539877 284887891374690589226227)
                ·
                  refine ⟨427331837062035883839341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284887891374690589226227 427331837062035883839341)
                  ·
                    refine ⟨160249438898263456439753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 427331837062035883839341 160249438898263456439753)
                    ·
                      rfl

theorem cell22_468127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_468127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468127 prefixEnd_468127 := by exact prefixLift 468127
  have htrace : WordTrace (prefixWord ++ tailWord_468127) baseStart_468127 baseEnd_468127 := by
    simpa [prefixWord, tailWord_468127, baseEnd_468127] using wordTrace_append hprefix tailTrace_468127
  have hstable : (prefixWord ++ tailWord_468127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468127).length < 2 ^ (prefixWord ++ tailWord_468127).sum := by decide
  have hdescent : baseEnd_468127 < baseStart_468127 := by decide
  rcases family_descends (prefixWord ++ tailWord_468127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468138 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_468138 : Nat := 118140960795 + 468138 * 2 ^ 59
def prefixEnd_468138 : Nat := 4983230072969 + 3 ^ 40 * 468138 * 2
def baseEnd_468138 : Nat := 160253204423063094414719

theorem tailTrace_468138 : CollatzResearch.WordTrace tailWord_468138 prefixEnd_468138 160253204423063094414719 := by
  unfold tailWord_468138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268598894505863112559267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11382930385348968300158045 4268598894505863112559267)
  ·
    refine ⟨6402898341758794668838901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268598894505863112559267 6402898341758794668838901)
    ·
      refine ⟨600271719539887000203647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6402898341758794668838901 600271719539887000203647)
      ·
        refine ⟨900407579309830500305471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600271719539887000203647 900407579309830500305471)
        ·
          refine ⟨1350611368964745750458207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900407579309830500305471 1350611368964745750458207)
          ·
            refine ⟨2025917053447118625687311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350611368964745750458207 2025917053447118625687311)
            ·
              refine ⟨3038875580170677938530967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025917053447118625687311 3038875580170677938530967)
              ·
                refine ⟨4558313370256016907796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038875580170677938530967 4558313370256016907796451)
                ·
                  refine ⟨6837470055384025361694677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558313370256016907796451 6837470055384025361694677)
                  ·
                    refine ⟨160253204423063094414719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6837470055384025361694677 160253204423063094414719)
                    ·
                      rfl

theorem cell22_468138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_468138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468138 prefixEnd_468138 := by exact prefixLift 468138
  have htrace : WordTrace (prefixWord ++ tailWord_468138) baseStart_468138 baseEnd_468138 := by
    simpa [prefixWord, tailWord_468138, baseEnd_468138] using wordTrace_append hprefix tailTrace_468138
  have hstable : (prefixWord ++ tailWord_468138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468138).length < 2 ^ (prefixWord ++ tailWord_468138).sum := by decide
  have hdescent : baseEnd_468138 < baseStart_468138 := by decide
  rcases family_descends (prefixWord ++ tailWord_468138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468151 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 6]
def baseStart_468151 : Nat := 118140960795 + 468151 * 2 ^ 59
def prefixEnd_468151 : Nat := 4983230072969 + 3 ^ 40 * 468151 * 2
def baseEnd_468151 : Nat := 53419218196245131279893

theorem tailTrace_468151 : CollatzResearch.WordTrace tailWord_468151 prefixEnd_468151 53419218196245131279893 := by
  unfold tailWord_468151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074869726976355670460307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11383246484650903780306871 17074869726976355670460307)
  ·
    refine ⟨25612304590464533505690461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17074869726976355670460307 25612304590464533505690461)
    ·
      refine ⟨9604614221424200064633923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25612304590464533505690461 9604614221424200064633923)
      ·
        refine ⟨14406921332136300096950885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604614221424200064633923 14406921332136300096950885)
        ·
          refine ⟨2701297749775556268178291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14406921332136300096950885 2701297749775556268178291)
          ·
            refine ⟨4051946624663334402267437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701297749775556268178291 4051946624663334402267437)
            ·
              refine ⟨1519479984248750400850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4051946624663334402267437 1519479984248750400850289)
              ·
                refine ⟨1139609988186562800637717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519479984248750400850289 1139609988186562800637717)
                ·
                  refine ⟨53419218196245131279893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1139609988186562800637717 53419218196245131279893)
                  ·
                    rfl

theorem cell22_468151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_468151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468151 prefixEnd_468151 := by exact prefixLift 468151
  have htrace : WordTrace (prefixWord ++ tailWord_468151) baseStart_468151 baseEnd_468151 := by
    simpa [prefixWord, tailWord_468151, baseEnd_468151] using wordTrace_append hprefix tailTrace_468151
  have hstable : (prefixWord ++ tailWord_468151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468151).length < 2 ^ (prefixWord ++ tailWord_468151).sum := by decide
  have hdescent : baseEnd_468151 < baseStart_468151 := by decide
  rcases family_descends (prefixWord ++ tailWord_468151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468168 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_468168 : Nat := 118140960795 + 468168 * 2 ^ 59
def prefixEnd_468168 : Nat := 4983230072969 + 3 ^ 40 * 468168 * 2
def baseEnd_468168 : Nat := 53421158012051005388209

theorem tailTrace_468168 : CollatzResearch.WordTrace tailWord_468168 prefixEnd_468168 53421158012051005388209 := by
  unfold tailWord_468168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537744883957383786914579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11383659845276511715886105 8537744883957383786914579)
  ·
    refine ⟨12806617325936075680371869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8537744883957383786914579 12806617325936075680371869)
    ·
      refine ⟨4802481497226028380139451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12806617325936075680371869 4802481497226028380139451)
      ·
        refine ⟨7203722245839042570209177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802481497226028380139451 7203722245839042570209177)
        ·
          refine ⟨5402791684379281927656883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7203722245839042570209177 5402791684379281927656883)
          ·
            refine ⟨8104187526568922891485325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402791684379281927656883 8104187526568922891485325)
            ·
              refine ⟨3039070322463346084306997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8104187526568922891485325 3039070322463346084306997)
              ·
                refine ⟨284912842730938695403781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3039070322463346084306997 284912842730938695403781)
                ·
                  refine ⟨53421158012051005388209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284912842730938695403781 53421158012051005388209)
                  ·
                    rfl

theorem cell22_468168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_468168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468168 prefixEnd_468168 := by exact prefixLift 468168
  have htrace : WordTrace (prefixWord ++ tailWord_468168) baseStart_468168 baseEnd_468168 := by
    simpa [prefixWord, tailWord_468168, baseEnd_468168] using wordTrace_append hprefix tailTrace_468168
  have hstable : (prefixWord ++ tailWord_468168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468168).length < 2 ^ (prefixWord ++ tailWord_468168).sum := by decide
  have hdescent : baseEnd_468168 < baseStart_468168 := by decide
  rcases family_descends (prefixWord ++ tailWord_468168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468170 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_468170 : Nat := 118140960795 + 468170 * 2 ^ 59
def prefixEnd_468170 : Nat := 4983230072969 + 3 ^ 40 * 468170 * 2
def baseEnd_468170 : Nat := 160264158677025677614621

theorem tailTrace_468170 : CollatzResearch.WordTrace tailWord_468170 prefixEnd_468170 160264158677025677614621 := by
  unfold tailWord_468170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268890678476880478850491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11383708475938347943601309 4268890678476880478850491)
  ·
    refine ⟨6403336017715320718275737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268890678476880478850491 6403336017715320718275737)
    ·
      refine ⟨4802502013286490538706803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6403336017715320718275737 4802502013286490538706803)
      ·
        refine ⟨7203753019929735808060205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802502013286490538706803 7203753019929735808060205)
        ·
          refine ⟨2701407382473650928022577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7203753019929735808060205 2701407382473650928022577)
          ·
            refine ⟨2026055536855238196016933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701407382473650928022577 2026055536855238196016933)
            ·
              refine ⟨379885413160357161753175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2026055536855238196016933 379885413160357161753175)
              ·
                refine ⟨569828119740535742629763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379885413160357161753175 569828119740535742629763)
                ·
                  refine ⟨854742179610803613944645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569828119740535742629763 854742179610803613944645)
                  ·
                    refine ⟨160264158677025677614621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 854742179610803613944645 160264158677025677614621)
                    ·
                      rfl

theorem cell22_468170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_468170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468170 prefixEnd_468170 := by exact prefixLift 468170
  have htrace : WordTrace (prefixWord ++ tailWord_468170) baseStart_468170 baseEnd_468170 := by
    simpa [prefixWord, tailWord_468170, baseEnd_468170] using wordTrace_append hprefix tailTrace_468170
  have hstable : (prefixWord ++ tailWord_468170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468170).length < 2 ^ (prefixWord ++ tailWord_468170).sum := by decide
  have hdescent : baseEnd_468170 < baseStart_468170 := by decide
  rcases family_descends (prefixWord ++ tailWord_468170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468241 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 7]
def baseStart_468241 : Nat := 118140960795 + 468241 * 2 ^ 59
def prefixEnd_468241 : Nat := 4983230072969 + 3 ^ 40 * 468241 * 2
def baseEnd_468241 : Nat := 53429487809335053029801

theorem tailTrace_468241 : CollatzResearch.WordTrace tailWord_468241 prefixEnd_468241 53429487809335053029801 := by
  unfold tailWord_468241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078152296650301041236577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11385434864433534027491051 17078152296650301041236577)
  ·
    refine ⟨12808614222487725780927433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17078152296650301041236577 12808614222487725780927433)
    ·
      refine ⟨9606460666865794335695575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12808614222487725780927433 9606460666865794335695575)
      ·
        refine ⟨14409691000298691503543363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9606460666865794335695575 14409691000298691503543363)
        ·
          refine ⟨21614536500448037255315045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409691000298691503543363 21614536500448037255315045)
          ·
            refine ⟨4052725593834006985371571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21614536500448037255315045 4052725593834006985371571)
            ·
              refine ⟨6079088390751010478057357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052725593834006985371571 6079088390751010478057357)
              ·
                refine ⟨2279658146531628929271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6079088390751010478057357 2279658146531628929271509)
                ·
                  refine ⟨53429487809335053029801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2279658146531628929271509 53429487809335053029801)
                  ·
                    rfl

theorem cell22_468241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_468241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468241 prefixEnd_468241 := by exact prefixLift 468241
  have htrace : WordTrace (prefixWord ++ tailWord_468241) baseStart_468241 baseEnd_468241 := by
    simpa [prefixWord, tailWord_468241, baseEnd_468241] using wordTrace_append hprefix tailTrace_468241
  have hstable : (prefixWord ++ tailWord_468241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468241).length < 2 ^ (prefixWord ++ tailWord_468241).sum := by decide
  have hdescent : baseEnd_468241 < baseStart_468241 := by decide
  rcases family_descends (prefixWord ++ tailWord_468241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468292 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_468292 : Nat := 118140960795 + 468292 * 2 ^ 59
def prefixEnd_468292 : Nat := 4983230072969 + 3 ^ 40 * 468292 * 2
def baseEnd_468292 : Nat := 53435307256752675354749

theorem tailTrace_468292 : CollatzResearch.WordTrace tailWord_468292 prefixEnd_468292 53435307256752675354749 := by
  unfold tailWord_468292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540006209732768375671565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11386674946310357834228753 8540006209732768375671565)
  ·
    refine ⟨3202502328649788140876837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8540006209732768375671565 3202502328649788140876837)
    ·
      refine ⟨600469186621835276414407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3202502328649788140876837 600469186621835276414407)
      ·
        refine ⟨900703779932752914621611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600469186621835276414407 900703779932752914621611)
        ·
          refine ⟨1351055669899129371932417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900703779932752914621611 1351055669899129371932417)
          ·
            refine ⟨1013291752424347028949313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351055669899129371932417 1013291752424347028949313)
            ·
              refine ⟨759968814318260271711985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013291752424347028949313 759968814318260271711985)
              ·
                refine ⟨569976610738695203783989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759968814318260271711985 569976610738695203783989)
                ·
                  refine ⟨53435307256752675354749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569976610738695203783989 53435307256752675354749)
                  ·
                    rfl

theorem cell22_468292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_468292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468292 prefixEnd_468292 := by exact prefixLift 468292
  have htrace : WordTrace (prefixWord ++ tailWord_468292) baseStart_468292 baseEnd_468292 := by
    simpa [prefixWord, tailWord_468292, baseEnd_468292] using wordTrace_append hprefix tailTrace_468292
  have hstable : (prefixWord ++ tailWord_468292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468292).length < 2 ^ (prefixWord ++ tailWord_468292).sum := by decide
  have hdescent : baseEnd_468292 < baseStart_468292 := by decide
  rcases family_descends (prefixWord ++ tailWord_468292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468354 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_468354 : Nat := 118140960795 + 468354 * 2 ^ 59
def prefixEnd_468354 : Nat := 4983230072969 + 3 ^ 40 * 468354 * 2
def baseEnd_468354 : Nat := 53442381879103510338019

theorem tailTrace_468354 : CollatzResearch.WordTrace tailWord_468354 prefixEnd_468354 53442381879103510338019 := by
  unfold tailWord_468354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270568436310230335025029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11388182496827280893400077 4270568436310230335025029)
  ·
    refine ⟨800731581808168187817193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4270568436310230335025029 800731581808168187817193)
    ·
      refine ⟨600548686356126140862895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 800731581808168187817193 600548686356126140862895)
      ·
        refine ⟨900823029534189211294343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600548686356126140862895 900823029534189211294343)
        ·
          refine ⟨1351234544301283816941515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900823029534189211294343 1351234544301283816941515)
          ·
            refine ⟨2026851816451925725412273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351234544301283816941515 2026851816451925725412273)
            ·
              refine ⟨1520138862338944294059205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026851816451925725412273 1520138862338944294059205)
              ·
                refine ⟨285026036688552055136101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1520138862338944294059205 285026036688552055136101)
                ·
                  refine ⟨53442381879103510338019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285026036688552055136101 53442381879103510338019)
                  ·
                    rfl

theorem cell22_468354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_468354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468354 prefixEnd_468354 := by exact prefixLift 468354
  have htrace : WordTrace (prefixWord ++ tailWord_468354) baseStart_468354 baseEnd_468354 := by
    simpa [prefixWord, tailWord_468354, baseEnd_468354] using wordTrace_append hprefix tailTrace_468354
  have hstable : (prefixWord ++ tailWord_468354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468354).length < 2 ^ (prefixWord ++ tailWord_468354).sum := by decide
  have hdescent : baseEnd_468354 < baseStart_468354 := by decide
  rcases family_descends (prefixWord ++ tailWord_468354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468382 : List Nat := [4, 3, 1, 2, 2, 1, 1, 8]
def baseStart_468382 : Nat := 118140960795 + 468382 * 2 ^ 59
def prefixEnd_468382 : Nat := 4983230072969 + 3 ^ 40 * 468382 * 2
def baseEnd_468382 : Nat := 17815192289947532368219

theorem tailTrace_468382 : CollatzResearch.WordTrace tailWord_468382 prefixEnd_468382 17815192289947532368219 := by
  unfold tailWord_468382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135411873642435265264925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11388863326092988081412933 2135411873642435265264925)
  ·
    refine ⟨800779452615913224474347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2135411873642435265264925 800779452615913224474347)
    ·
      refine ⟨1201169178923869836711521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800779452615913224474347 1201169178923869836711521)
      ·
        refine ⟨900876884192902377533641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1201169178923869836711521 900876884192902377533641)
        ·
          refine ⟨675657663144676783150231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900876884192902377533641 675657663144676783150231)
          ·
            refine ⟨1013486494717015174725347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675657663144676783150231 1013486494717015174725347)
            ·
              refine ⟨1520229742075522762088021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013486494717015174725347 1520229742075522762088021)
              ·
                refine ⟨17815192289947532368219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1520229742075522762088021 17815192289947532368219)
                ·
                  rfl

theorem cell22_468382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_468382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468382 prefixEnd_468382 := by exact prefixLift 468382
  have htrace : WordTrace (prefixWord ++ tailWord_468382) baseStart_468382 baseEnd_468382 := by
    simpa [prefixWord, tailWord_468382, baseEnd_468382] using wordTrace_append hprefix tailTrace_468382
  have hstable : (prefixWord ++ tailWord_468382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468382).length < 2 ^ (prefixWord ++ tailWord_468382).sum := by decide
  have hdescent : baseEnd_468382 < baseStart_468382 := by decide
  rcases family_descends (prefixWord ++ tailWord_468382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468408 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_468408 : Nat := 118140960795 + 468408 * 2 ^ 59
def prefixEnd_468408 : Nat := 4983230072969 + 3 ^ 40 * 468408 * 2
def baseEnd_468408 : Nat := 160345630940872390163891

theorem tailTrace_468408 : CollatzResearch.WordTrace tailWord_468408 prefixEnd_468408 160345630940872390163891 := by
  unfold tailWord_468408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542121643522644281282939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11389495524696859041710585 8542121643522644281282939)
  ·
    refine ⟨12813182465283966421924409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8542121643522644281282939 12813182465283966421924409)
    ·
      refine ⟨9609886848962974816443307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12813182465283966421924409 9609886848962974816443307)
      ·
        refine ⟨14414830273444462224664961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609886848962974816443307 14414830273444462224664961)
        ·
          refine ⟨10811122705083346668498721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14414830273444462224664961 10811122705083346668498721)
          ·
            refine ⟨8108342028812510001374041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811122705083346668498721 8108342028812510001374041)
            ·
              refine ⟨6081256521609382501030531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108342028812510001374041 6081256521609382501030531)
              ·
                refine ⟨9121884782414073751545797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081256521609382501030531 9121884782414073751545797)
                ·
                  refine ⟨1710353396702638828414837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9121884782414073751545797 1710353396702638828414837)
                  ·
                    refine ⟨160345630940872390163891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710353396702638828414837 160345630940872390163891)
                    ·
                      rfl

theorem cell22_468408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_468408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468408 prefixEnd_468408 := by exact prefixLift 468408
  have htrace : WordTrace (prefixWord ++ tailWord_468408) baseStart_468408 baseEnd_468408 := by
    simpa [prefixWord, tailWord_468408, baseEnd_468408] using wordTrace_append hprefix tailTrace_468408
  have hstable : (prefixWord ++ tailWord_468408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468408).length < 2 ^ (prefixWord ++ tailWord_468408).sum := by decide
  have hdescent : baseEnd_468408 < baseStart_468408 := by decide
  rcases family_descends (prefixWord ++ tailWord_468408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468472 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_468472 : Nat := 118140960795 + 468472 * 2 ^ 59
def prefixEnd_468472 : Nat := 4983230072969 + 3 ^ 40 * 468472 * 2
def baseEnd_468472 : Nat := 53455846482932518854565

theorem tailTrace_468472 : CollatzResearch.WordTrace tailWord_468472 prefixEnd_468472 53455846482932518854565 := by
  unfold tailWord_468472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543288779406713746447835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11391051705875618328597113 8543288779406713746447835)
  ·
    refine ⟨12814933169110070619671753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543288779406713746447835 12814933169110070619671753)
    ·
      refine ⟨9611199876832552964753815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12814933169110070619671753 9611199876832552964753815)
      ·
        refine ⟨14416799815248829447130723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611199876832552964753815 14416799815248829447130723)
        ·
          refine ⟨21625199722873244170696085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416799815248829447130723 21625199722873244170696085)
          ·
            refine ⟨1013681237009683320501379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21625199722873244170696085 1013681237009683320501379)
            ·
              refine ⟨1520521855514524980752069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013681237009683320501379 1520521855514524980752069)
              ·
                refine ⟨285097847908973433891013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1520521855514524980752069 285097847908973433891013)
                ·
                  refine ⟨53455846482932518854565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285097847908973433891013 53455846482932518854565)
                  ·
                    rfl

theorem cell22_468472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_468472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468472 prefixEnd_468472 := by exact prefixLift 468472
  have htrace : WordTrace (prefixWord ++ tailWord_468472) baseStart_468472 baseEnd_468472 := by
    simpa [prefixWord, tailWord_468472, baseEnd_468472] using wordTrace_append hprefix tailTrace_468472
  have hstable : (prefixWord ++ tailWord_468472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468472).length < 2 ^ (prefixWord ++ tailWord_468472).sum := by decide
  have hdescent : baseEnd_468472 < baseStart_468472 := by decide
  rcases family_descends (prefixWord ++ tailWord_468472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468483 : List Nat := [1, 1, 1, 3, 2, 1, 2, 11]
def baseStart_468483 : Nat := 118140960795 + 468483 * 2 ^ 59
def prefixEnd_468483 : Nat := 4983230072969 + 3 ^ 40 * 468483 * 2
def baseEnd_468483 : Nat := 17819033885955243837629

theorem tailTrace_468483 : CollatzResearch.WordTrace tailWord_468483 prefixEnd_468483 17819033885955243837629 := by
  unfold tailWord_468483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086978761773576371546103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11391319174515717581030735 17086978761773576371546103)
  ·
    refine ⟨25630468142660364557319155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17086978761773576371546103 25630468142660364557319155)
    ·
      refine ⟨38445702213990546835978733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25630468142660364557319155 38445702213990546835978733)
      ·
        refine ⟨14417138330246455063492025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38445702213990546835978733 14417138330246455063492025)
        ·
          refine ⟨10812853747684841297619019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14417138330246455063492025 10812853747684841297619019)
          ·
            refine ⟨16219280621527261946428529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812853747684841297619019 16219280621527261946428529)
            ·
              refine ⟨12164460466145446459821397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16219280621527261946428529 12164460466145446459821397)
              ·
                refine ⟨17819033885955243837629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12164460466145446459821397 17819033885955243837629)
                ·
                  rfl

theorem cell22_468483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_468483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468483 prefixEnd_468483 := by exact prefixLift 468483
  have htrace : WordTrace (prefixWord ++ tailWord_468483) baseStart_468483 baseEnd_468483 := by
    simpa [prefixWord, tailWord_468483, baseEnd_468483] using wordTrace_append hprefix tailTrace_468483
  have hstable : (prefixWord ++ tailWord_468483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468483).length < 2 ^ (prefixWord ++ tailWord_468483).sum := by decide
  have hdescent : baseEnd_468483 < baseStart_468483 := by decide
  rcases family_descends (prefixWord ++ tailWord_468483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468487 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_468487 : Nat := 118140960795 + 468487 * 2 ^ 59
def prefixEnd_468487 : Nat := 4983230072969 + 3 ^ 40 * 468487 * 2
def baseEnd_468487 : Nat := 160372674255342517438649

theorem tailTrace_468487 : CollatzResearch.WordTrace tailWord_468487 prefixEnd_468487 160372674255342517438649 := by
  unfold tailWord_468487
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087124653759085054691715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11391416435839390036461143 17087124653759085054691715)
  ·
    refine ⟨25630686980638627582037573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17087124653759085054691715 25630686980638627582037573)
    ·
      refine ⟨4805753808869742671632045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25630686980638627582037573 4805753808869742671632045)
      ·
        refine ⟨1802157678326153501862017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4805753808869742671632045 1802157678326153501862017)
        ·
          refine ⟨1351618258744615126396513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802157678326153501862017 1351618258744615126396513)
          ·
            refine ⟨1013713694058461344797385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351618258744615126396513 1013713694058461344797385)
            ·
              refine ⟨760285270543846008598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013713694058461344797385 760285270543846008598039)
              ·
                refine ⟨1140427905815769012897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760285270543846008598039 1140427905815769012897059)
                ·
                  refine ⟨1710641858723653519345589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140427905815769012897059 1710641858723653519345589)
                  ·
                    refine ⟨160372674255342517438649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710641858723653519345589 160372674255342517438649)
                    ·
                      rfl

theorem cell22_468487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_468487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468487 prefixEnd_468487 := by exact prefixLift 468487
  have htrace : WordTrace (prefixWord ++ tailWord_468487) baseStart_468487 baseEnd_468487 := by
    simpa [prefixWord, tailWord_468487, baseEnd_468487] using wordTrace_append hprefix tailTrace_468487
  have hstable : (prefixWord ++ tailWord_468487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468487).length < 2 ^ (prefixWord ++ tailWord_468487).sum := by decide
  have hdescent : baseEnd_468487 < baseStart_468487 := by decide
  rcases family_descends (prefixWord ++ tailWord_468487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468575 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_468575 : Nat := 118140960795 + 468575 * 2 ^ 59
def prefixEnd_468575 : Nat := 4983230072969 + 3 ^ 40 * 468575 * 2
def baseEnd_468575 : Nat := 160402798453739621238379

theorem tailTrace_468575 : CollatzResearch.WordTrace tailWord_468575 prefixEnd_468575 160402798453739621238379 := by
  unfold tailWord_468575
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090334277440276083895179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11393556184960184055930119 17090334277440276083895179)
  ·
    refine ⟨25635501416160414125842769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17090334277440276083895179 25635501416160414125842769)
    ·
      refine ⟨19226626062120310594382077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25635501416160414125842769 19226626062120310594382077)
      ·
        refine ⟨7209984773295116472893279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19226626062120310594382077 7209984773295116472893279)
        ·
          refine ⟨10814977159942674709339919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209984773295116472893279 10814977159942674709339919)
          ·
            refine ⟨16222465739914012064009879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814977159942674709339919 16222465739914012064009879)
            ·
              refine ⟨24333698609871018096014819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16222465739914012064009879 24333698609871018096014819)
              ·
                refine ⟨36500547914806527144022229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24333698609871018096014819 36500547914806527144022229)
                ·
                  refine ⟨855481591753277979938021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 36500547914806527144022229 855481591753277979938021)
                  ·
                    refine ⟨160402798453739621238379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855481591753277979938021 160402798453739621238379)
                    ·
                      rfl

theorem cell22_468575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_468575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468575 prefixEnd_468575 := by exact prefixLift 468575
  have htrace : WordTrace (prefixWord ++ tailWord_468575) baseStart_468575 baseEnd_468575 := by
    simpa [prefixWord, tailWord_468575, baseEnd_468575] using wordTrace_append hprefix tailTrace_468575
  have hstable : (prefixWord ++ tailWord_468575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468575).length < 2 ^ (prefixWord ++ tailWord_468575).sum := by decide
  have hdescent : baseEnd_468575 < baseStart_468575 := by decide
  rcases family_descends (prefixWord ++ tailWord_468575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468609 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_468609 : Nat := 118140960795 + 468609 * 2 ^ 59
def prefixEnd_468609 : Nat := 4983230072969 + 3 ^ 40 * 468609 * 2
def baseEnd_468609 : Nat := 160414437348574865888275

theorem tailTrace_468609 : CollatzResearch.WordTrace tailWord_468609 prefixEnd_468609 160414437348574865888275 := by
  unfold tailWord_468609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17091574359317099890632881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11394382906211399927088587 17091574359317099890632881)
  ·
    refine ⟨12818680769487824917974661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17091574359317099890632881 12818680769487824917974661)
    ·
      refine ⟨2403502644278967172120249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12818680769487824917974661 2403502644278967172120249)
      ·
        refine ⟨1802626983209225379090187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403502644278967172120249 1802626983209225379090187)
        ·
          refine ⟨2703940474813838068635281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802626983209225379090187 2703940474813838068635281)
          ·
            refine ⟨2027955356110378551476461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703940474813838068635281 2027955356110378551476461)
            ·
              refine ⟨760483258541391956803673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2027955356110378551476461 760483258541391956803673)
              ·
                refine ⟨570362443906043967602755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760483258541391956803673 570362443906043967602755)
                ·
                  refine ⟨855543665859065951404133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570362443906043967602755 855543665859065951404133)
                  ·
                    refine ⟨160414437348574865888275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855543665859065951404133 160414437348574865888275)
                    ·
                      rfl

theorem cell22_468609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_468609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468609 prefixEnd_468609 := by exact prefixLift 468609
  have htrace : WordTrace (prefixWord ++ tailWord_468609) baseStart_468609 baseEnd_468609 := by
    simpa [prefixWord, tailWord_468609, baseEnd_468609] using wordTrace_append hprefix tailTrace_468609
  have hstable : (prefixWord ++ tailWord_468609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468609).length < 2 ^ (prefixWord ++ tailWord_468609).sum := by decide
  have hdescent : baseEnd_468609 < baseStart_468609 := by decide
  rcases family_descends (prefixWord ++ tailWord_468609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468622 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_468622 : Nat := 118140960795 + 468622 * 2 ^ 59
def prefixEnd_468622 : Nat := 4983230072969 + 3 ^ 40 * 468622 * 2
def baseEnd_468622 : Nat := 160418887514247165313235

theorem tailTrace_468622 : CollatzResearch.WordTrace tailWord_468622 prefixEnd_468622 160418887514247165313235 := by
  unfold tailWord_468622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136506063533750388857015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11394699005513335407237413 2136506063533750388857015)
  ·
    refine ⟨3204759095300625583285523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2136506063533750388857015 3204759095300625583285523)
    ·
      refine ⟨4807138642950938374928285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3204759095300625583285523 4807138642950938374928285)
      ·
        refine ⟨1802676991106601890598107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4807138642950938374928285 1802676991106601890598107)
        ·
          refine ⟨2704015486659902835897161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802676991106601890598107 2704015486659902835897161)
          ·
            refine ⟨2028011614994927126922871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704015486659902835897161 2028011614994927126922871)
            ·
              refine ⟨3042017422492390690384307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028011614994927126922871 3042017422492390690384307)
              ·
                refine ⟨4563026133738586035576461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042017422492390690384307 4563026133738586035576461)
                ·
                  refine ⟨1711134800151969763341173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4563026133738586035576461 1711134800151969763341173)
                  ·
                    refine ⟨160418887514247165313235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1711134800151969763341173 160418887514247165313235)
                    ·
                      rfl

theorem cell22_468622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_468622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468622 prefixEnd_468622 := by exact prefixLift 468622
  have htrace : WordTrace (prefixWord ++ tailWord_468622) baseStart_468622 baseEnd_468622 := by
    simpa [prefixWord, tailWord_468622, baseEnd_468622] using wordTrace_append hprefix tailTrace_468622
  have hstable : (prefixWord ++ tailWord_468622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468622).length < 2 ^ (prefixWord ++ tailWord_468622).sum := by decide
  have hdescent : baseEnd_468622 < baseStart_468622 := by decide
  rcases family_descends (prefixWord ++ tailWord_468622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468641 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 4]
def baseStart_468641 : Nat := 118140960795 + 468641 * 2 ^ 59
def prefixEnd_468641 : Nat := 4983230072969 + 3 ^ 40 * 468641 * 2
def baseEnd_468641 : Nat := 53475130534179149696059

theorem tailTrace_468641 : CollatzResearch.WordTrace tailWord_468641 prefixEnd_468641 53475130534179149696059 := by
  unfold tailWord_468641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17092741495201169355797777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11395160996800779570531851 17092741495201169355797777)
  ·
    refine ⟨12819556121400877016848333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17092741495201169355797777 12819556121400877016848333)
    ·
      refine ⟨4807333545525328881318125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12819556121400877016848333 4807333545525328881318125)
      ·
        refine ⟨1802750079571998330494297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4807333545525328881318125 1802750079571998330494297)
        ·
          refine ⟨1352062559678998747870723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802750079571998330494297 1352062559678998747870723)
          ·
            refine ⟨2028093839518498121806085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352062559678998747870723 2028093839518498121806085)
            ·
              refine ⟨380267594909718397838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2028093839518498121806085 380267594909718397838641)
              ·
                refine ⟨285200696182288798378981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380267594909718397838641 285200696182288798378981)
                ·
                  refine ⟨53475130534179149696059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285200696182288798378981 53475130534179149696059)
                  ·
                    rfl

theorem cell22_468641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_468641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468641 prefixEnd_468641 := by exact prefixLift 468641
  have htrace : WordTrace (prefixWord ++ tailWord_468641) baseStart_468641 baseEnd_468641 := by
    simpa [prefixWord, tailWord_468641, baseEnd_468641] using wordTrace_append hprefix tailTrace_468641
  have hstable : (prefixWord ++ tailWord_468641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468641).length < 2 ^ (prefixWord ++ tailWord_468641).sum := by decide
  have hdescent : baseEnd_468641 < baseStart_468641 := by decide
  rcases family_descends (prefixWord ++ tailWord_468641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468697 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 7]
def baseStart_468697 : Nat := 118140960795 + 468697 * 2 ^ 59
def prefixEnd_468697 : Nat := 4983230072969 + 3 ^ 40 * 468697 * 2
def baseEnd_468697 : Nat := 53481520515657323229335

theorem tailTrace_468697 : CollatzResearch.WordTrace tailWord_468697 prefixEnd_468697 53481520515657323229335 := by
  unfold tailWord_468697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17094783982998290919836345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11396522655332193946557563 17094783982998290919836345)
  ·
    refine ⟨12821087987248718189877259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17094783982998290919836345 12821087987248718189877259)
    ·
      refine ⟨19231631980873077284815889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821087987248718189877259 19231631980873077284815889)
      ·
        refine ⟨14423723985654807963611917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19231631980873077284815889 14423723985654807963611917)
        ·
          refine ⟨5408896494620552986354469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14423723985654807963611917 5408896494620552986354469)
          ·
            refine ⟨1014168092741353684941463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5408896494620552986354469 1014168092741353684941463)
            ·
              refine ⟨1521252139112030527412195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014168092741353684941463 1521252139112030527412195)
              ·
                refine ⟨2281878208668045791118293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521252139112030527412195 2281878208668045791118293)
                ·
                  refine ⟨53481520515657323229335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2281878208668045791118293 53481520515657323229335)
                  ·
                    rfl

theorem cell22_468697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_468697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468697 prefixEnd_468697 := by exact prefixLift 468697
  have htrace : WordTrace (prefixWord ++ tailWord_468697) baseStart_468697 baseEnd_468697 := by
    simpa [prefixWord, tailWord_468697, baseEnd_468697] using wordTrace_append hprefix tailTrace_468697
  have hstable : (prefixWord ++ tailWord_468697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468697).length < 2 ^ (prefixWord ++ tailWord_468697).sum := by decide
  have hdescent : baseEnd_468697 < baseStart_468697 := by decide
  rcases family_descends (prefixWord ++ tailWord_468697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468727 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_468727 : Nat := 118140960795 + 468727 * 2 ^ 59
def prefixEnd_468727 : Nat := 4983230072969 + 3 ^ 40 * 468727 * 2
def baseEnd_468727 : Nat := 160454831160061891437913

theorem tailTrace_468727 : CollatzResearch.WordTrace tailWord_468727 prefixEnd_468727 160454831160061891437913 := by
  unfold tailWord_468727
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095878172889606043428435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11397252115259737362285623 17095878172889606043428435)
  ·
    refine ⟨25643817259334409065142653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17095878172889606043428435 25643817259334409065142653)
    ·
      refine ⟨9616431472250403399428495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25643817259334409065142653 9616431472250403399428495)
      ·
        refine ⟨14424647208375605099142743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616431472250403399428495 14424647208375605099142743)
        ·
          refine ⟨21636970812563407648714115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14424647208375605099142743 21636970812563407648714115)
          ·
            refine ⟨32455456218845111473071173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21636970812563407648714115 32455456218845111473071173)
            ·
              refine ⟨6085398041033458401200845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32455456218845111473071173 6085398041033458401200845)
              ·
                refine ⟨2282024265387546900450317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6085398041033458401200845 2282024265387546900450317)
                ·
                  refine ⟨855759099520330087668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2282024265387546900450317 855759099520330087668869)
                  ·
                    refine ⟨160454831160061891437913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855759099520330087668869 160454831160061891437913)
                    ·
                      rfl

theorem cell22_468727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_468727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468727 prefixEnd_468727 := by exact prefixLift 468727
  have htrace : WordTrace (prefixWord ++ tailWord_468727) baseStart_468727 baseEnd_468727 := by
    simpa [prefixWord, tailWord_468727, baseEnd_468727] using wordTrace_append hprefix tailTrace_468727
  have hstable : (prefixWord ++ tailWord_468727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468727).length < 2 ^ (prefixWord ++ tailWord_468727).sum := by decide
  have hdescent : baseEnd_468727 < baseStart_468727 := by decide
  rcases family_descends (prefixWord ++ tailWord_468727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468744 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_468744 : Nat := 118140960795 + 468744 * 2 ^ 59
def prefixEnd_468744 : Nat := 4983230072969 + 3 ^ 40 * 468744 * 2
def baseEnd_468744 : Nat := 160460650607479513762861

theorem tailTrace_468744 : CollatzResearch.WordTrace tailWord_468744 prefixEnd_468744 160460650607479513762861 := by
  unfold tailWord_468744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548249106914008973398643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11397665475885345297864857 8548249106914008973398643)
  ·
    refine ⟨12822373660371013460097965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548249106914008973398643 12822373660371013460097965)
    ·
      refine ⟨4808390122639130047536737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12822373660371013460097965 4808390122639130047536737)
      ·
        refine ⟨3606292591979347535652553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808390122639130047536737 3606292591979347535652553)
        ·
          refine ⟨2704719443984510651739415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606292591979347535652553 2704719443984510651739415)
          ·
            refine ⟨4057079165976765977609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704719443984510651739415 4057079165976765977609123)
            ·
              refine ⟨6085618748965148966413685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057079165976765977609123 6085618748965148966413685)
              ·
                refine ⟨570526757715482715601283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6085618748965148966413685 570526757715482715601283)
                ·
                  refine ⟨855790136573224073401925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570526757715482715601283 855790136573224073401925)
                  ·
                    refine ⟨160460650607479513762861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855790136573224073401925 160460650607479513762861)
                    ·
                      rfl

theorem cell22_468744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_468744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468744 prefixEnd_468744 := by exact prefixLift 468744
  have htrace : WordTrace (prefixWord ++ tailWord_468744) baseStart_468744 baseEnd_468744 := by
    simpa [prefixWord, tailWord_468744, baseEnd_468744] using wordTrace_append hprefix tailTrace_468744
  have hstable : (prefixWord ++ tailWord_468744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468744).length < 2 ^ (prefixWord ++ tailWord_468744).sum := by decide
  have hdescent : baseEnd_468744 < baseStart_468744 := by decide
  rcases family_descends (prefixWord ++ tailWord_468744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468759 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 6]
def baseStart_468759 : Nat := 118140960795 + 468759 * 2 ^ 59
def prefixEnd_468759 : Nat := 4983230072969 + 3 ^ 40 * 468759 * 2
def baseEnd_468759 : Nat := 53488595138008158212605

theorem tailTrace_468759 : CollatzResearch.WordTrace tailWord_468759 prefixEnd_468759 53488595138008158212605 := by
  unfold tailWord_468759
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097045308773675508593331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11398030205849117005728887 17097045308773675508593331)
  ·
    refine ⟨25645567963160513262889997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097045308773675508593331 25645567963160513262889997)
    ·
      refine ⟨9617087986185192473583749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25645567963160513262889997 9617087986185192473583749)
      ·
        refine ⟨1803203997409723588796953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9617087986185192473583749 1803203997409723588796953)
        ·
          refine ⟨1352402998057292691597715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803203997409723588796953 1352402998057292691597715)
          ·
            refine ⟨2028604497085939037396573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352402998057292691597715 2028604497085939037396573)
            ·
              refine ⟨760726686407227139023715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2028604497085939037396573 760726686407227139023715)
              ·
                refine ⟨1141090029610840708535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760726686407227139023715 1141090029610840708535573)
                ·
                  refine ⟨53488595138008158212605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1141090029610840708535573 53488595138008158212605)
                  ·
                    rfl

theorem cell22_468759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_468759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468759 prefixEnd_468759 := by exact prefixLift 468759
  have htrace : WordTrace (prefixWord ++ tailWord_468759) baseStart_468759 baseEnd_468759 := by
    simpa [prefixWord, tailWord_468759, baseEnd_468759] using wordTrace_append hprefix tailTrace_468759
  have hstable : (prefixWord ++ tailWord_468759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468759).length < 2 ^ (prefixWord ++ tailWord_468759).sum := by decide
  have hdescent : baseEnd_468759 < baseStart_468759 := by decide
  rcases family_descends (prefixWord ++ tailWord_468759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468904 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_468904 : Nat := 118140960795 + 468904 * 2 ^ 59
def prefixEnd_468904 : Nat := 4983230072969 + 3 ^ 40 * 468904 * 2
def baseEnd_468904 : Nat := 160515421877292429762371

theorem tailTrace_468904 : CollatzResearch.WordTrace tailWord_468904 prefixEnd_468904 160515421877292429762371 := by
  unfold tailWord_468904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551166946624182636310883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11401555928832243515081177 8551166946624182636310883)
  ·
    refine ⟨12826750419936273954466325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8551166946624182636310883 12826750419936273954466325)
    ·
      refine ⟨601253925934512841615609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12826750419936273954466325 601253925934512841615609)
      ·
        refine ⟨450940444450884631211707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601253925934512841615609 450940444450884631211707)
        ·
          refine ⟨676410666676326946817561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450940444450884631211707 676410666676326946817561)
          ·
            refine ⟨507308000007245210113171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676410666676326946817561 507308000007245210113171)
            ·
              refine ⟨760962000010867815169757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507308000007245210113171 760962000010867815169757)
              ·
                refine ⟨285360750004075430688659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760962000010867815169757 285360750004075430688659)
                ·
                  refine ⟨428041125006113146032989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285360750004075430688659 428041125006113146032989)
                  ·
                    refine ⟨160515421877292429762371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428041125006113146032989 160515421877292429762371)
                    ·
                      rfl

theorem cell22_468904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_468904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468904 prefixEnd_468904 := by exact prefixLift 468904
  have htrace : WordTrace (prefixWord ++ tailWord_468904) baseStart_468904 baseEnd_468904 := by
    simpa [prefixWord, tailWord_468904, baseEnd_468904] using wordTrace_append hprefix tailTrace_468904
  have hstable : (prefixWord ++ tailWord_468904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468904).length < 2 ^ (prefixWord ++ tailWord_468904).sum := by decide
  have hdescent : baseEnd_468904 < baseStart_468904 := by decide
  rcases family_descends (prefixWord ++ tailWord_468904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468928 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_468928 : Nat := 118140960795 + 468928 * 2 ^ 59
def prefixEnd_468928 : Nat := 4983230072969 + 3 ^ 40 * 468928 * 2
def baseEnd_468928 : Nat := 53507879189254789054099

theorem tailTrace_468928 : CollatzResearch.WordTrace tailWord_468928 prefixEnd_468928 53507879189254789054099 := by
  unfold tailWord_468928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551604622580708685747719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11402139496774278247663625 8551604622580708685747719)
  ·
    refine ⟨12827406933871063028621579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8551604622580708685747719 12827406933871063028621579)
    ·
      refine ⟨19241110400806594542932369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12827406933871063028621579 19241110400806594542932369)
      ·
        refine ⟨14430832800604945907199277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19241110400806594542932369 14430832800604945907199277)
        ·
          refine ⟨5411562300226854715199729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14430832800604945907199277 5411562300226854715199729)
          ·
            refine ⟨4058671725170141036399797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411562300226854715199729 4058671725170141036399797)
            ·
              refine ⟨380500474234700722162481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4058671725170141036399797 380500474234700722162481)
              ·
                refine ⟨285375355676025541621861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380500474234700722162481 285375355676025541621861)
                ·
                  refine ⟨53507879189254789054099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285375355676025541621861 53507879189254789054099)
                  ·
                    rfl

theorem cell22_468928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_468928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468928 prefixEnd_468928 := by exact prefixLift 468928
  have htrace : WordTrace (prefixWord ++ tailWord_468928) baseStart_468928 baseEnd_468928 := by
    simpa [prefixWord, tailWord_468928, baseEnd_468928] using wordTrace_append hprefix tailTrace_468928
  have hstable : (prefixWord ++ tailWord_468928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468928).length < 2 ^ (prefixWord ++ tailWord_468928).sum := by decide
  have hdescent : baseEnd_468928 < baseStart_468928 := by decide
  rcases family_descends (prefixWord ++ tailWord_468928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468939 : List Nat := [1, 1, 1, 1, 3, 4, 4, 7]
def baseStart_468939 : Nat := 118140960795 + 468939 * 2 ^ 59
def prefixEnd_468939 : Nat := 4983230072969 + 3 ^ 40 * 468939 * 2
def baseEnd_468939 : Nat := 17836378121396000570807

theorem tailTrace_468939 : CollatzResearch.WordTrace tailWord_468939 prefixEnd_468939 17836378121396000570807 := by
  unfold tailWord_468939
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103610448121566250145871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11402406965414377500097247 17103610448121566250145871)
  ·
    refine ⟨25655415672182349375218807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17103610448121566250145871 25655415672182349375218807)
    ·
      refine ⟨38483123508273524062828211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25655415672182349375218807 38483123508273524062828211)
      ·
        refine ⟨57724685262410286094242317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38483123508273524062828211 57724685262410286094242317)
        ·
          refine ⟨21646756973403857285340869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57724685262410286094242317 21646756973403857285340869)
          ·
            refine ⟨4058766932513223241001413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21646756973403857285340869 4058766932513223241001413)
            ·
              refine ⟨761018799846229357687765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4058766932513223241001413 761018799846229357687765)
              ·
                refine ⟨17836378121396000570807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 761018799846229357687765 17836378121396000570807)
                ·
                  rfl

theorem cell22_468939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 7].length) (baseStart_468939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468939 prefixEnd_468939 := by exact prefixLift 468939
  have htrace : WordTrace (prefixWord ++ tailWord_468939) baseStart_468939 baseEnd_468939 := by
    simpa [prefixWord, tailWord_468939, baseEnd_468939] using wordTrace_append hprefix tailTrace_468939
  have hstable : (prefixWord ++ tailWord_468939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468939).length < 2 ^ (prefixWord ++ tailWord_468939).sum := by decide
  have hdescent : baseEnd_468939 < baseStart_468939 := by decide
  rcases family_descends (prefixWord ++ tailWord_468939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468973 : List Nat := [1, 5, 1, 4, 2, 9]
def baseStart_468973 : Nat := 118140960795 + 468973 * 2 ^ 59
def prefixEnd_468973 : Nat := 4983230072969 + 3 ^ 40 * 468973 * 2
def baseEnd_468973 : Nat := 1981963481325916664039

theorem tailTrace_468973 : CollatzResearch.WordTrace tailWord_468973 prefixEnd_468973 1981963481325916664039 := by
  unfold tailWord_468973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104850529998390056883573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11403233686665593371255715 17104850529998390056883573)
  ·
    refine ⟨1603579737187349067832835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17104850529998390056883573 1603579737187349067832835)
    ·
      refine ⟨2405369605781023601749253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603579737187349067832835 2405369605781023601749253)
      ·
        refine ⟨451006801083941925327985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2405369605781023601749253 451006801083941925327985)
        ·
          refine ⟨338255100812956443995989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451006801083941925327985 338255100812956443995989)
          ·
            refine ⟨1981963481325916664039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 338255100812956443995989 1981963481325916664039)
            ·
              rfl

theorem cell22_468973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 9].length) (baseStart_468973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468973 prefixEnd_468973 := by exact prefixLift 468973
  have htrace : WordTrace (prefixWord ++ tailWord_468973) baseStart_468973 baseEnd_468973 := by
    simpa [prefixWord, tailWord_468973, baseEnd_468973] using wordTrace_append hprefix tailTrace_468973
  have hstable : (prefixWord ++ tailWord_468973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468973).length < 2 ^ (prefixWord ++ tailWord_468973).sum := by decide
  have hdescent : baseEnd_468973 < baseStart_468973 := by decide
  rcases family_descends (prefixWord ++ tailWord_468973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468984 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_468984 : Nat := 118140960795 + 468984 * 2 ^ 59
def prefixEnd_468984 : Nat := 4983230072969 + 3 ^ 40 * 468984 * 2
def baseEnd_468984 : Nat := 53514269170732962587375

theorem tailTrace_468984 : CollatzResearch.WordTrace tailWord_468984 prefixEnd_468984 53514269170732962587375 := by
  unfold tailWord_468984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552625866479269467767003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11403501155305692623689337 8552625866479269467767003)
  ·
    refine ⟨12828938799718904201650505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552625866479269467767003 12828938799718904201650505)
    ·
      refine ⟨9621704099789178151237879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828938799718904201650505 9621704099789178151237879)
      ·
        refine ⟨14432556149683767226856819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621704099789178151237879 14432556149683767226856819)
        ·
          refine ⟨21648834224525650840285229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14432556149683767226856819 21648834224525650840285229)
          ·
            refine ⟨8118312834197119065106961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21648834224525650840285229 8118312834197119065106961)
            ·
              refine ⟨6088734625647839298830221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8118312834197119065106961 6088734625647839298830221)
              ·
                refine ⟨2283275484617939737061333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6088734625647839298830221 2283275484617939737061333)
                ·
                  refine ⟨53514269170732962587375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2283275484617939737061333 53514269170732962587375)
                  ·
                    rfl

theorem cell22_468984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_468984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_468984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_468984 prefixEnd_468984 := by exact prefixLift 468984
  have htrace : WordTrace (prefixWord ++ tailWord_468984) baseStart_468984 baseEnd_468984 := by
    simpa [prefixWord, tailWord_468984, baseEnd_468984] using wordTrace_append hprefix tailTrace_468984
  have hstable : (prefixWord ++ tailWord_468984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468984).length < 2 ^ (prefixWord ++ tailWord_468984).sum := by decide
  have hdescent : baseEnd_468984 < baseStart_468984 := by decide
  rcases family_descends (prefixWord ++ tailWord_468984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469080 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_469080 : Nat := 118140960795 + 469080 * 2 ^ 59
def prefixEnd_469080 : Nat := 4983230072969 + 3 ^ 40 * 469080 * 2
def baseEnd_469080 : Nat := 53525223424695545787277

theorem tailTrace_469080 : CollatzResearch.WordTrace tailWord_469080 prefixEnd_469080 53525223424695545787277 := by
  unfold tailWord_469080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554376570305373665514347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11405835427073831554019129 8554376570305373665514347)
  ·
    refine ⟨12831564855458060498271521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8554376570305373665514347 12831564855458060498271521)
    ·
      refine ⟨9623673641593545373703641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12831564855458060498271521 9623673641593545373703641)
      ·
        refine ⟨7217755231195159030277731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9623673641593545373703641 7217755231195159030277731)
        ·
          refine ⟨10826632846792738545416597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217755231195159030277731 10826632846792738545416597)
          ·
            refine ⟨507498414693409619316403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10826632846792738545416597 507498414693409619316403)
            ·
              refine ⟨761247622040114428974605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507498414693409619316403 761247622040114428974605)
              ·
                refine ⟨285467858265042910865477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761247622040114428974605 285467858265042910865477)
                ·
                  refine ⟨53525223424695545787277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285467858265042910865477 53525223424695545787277)
                  ·
                    rfl

theorem cell22_469080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_469080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469080 prefixEnd_469080 := by exact prefixLift 469080
  have htrace : WordTrace (prefixWord ++ tailWord_469080) baseStart_469080 baseEnd_469080 := by
    simpa [prefixWord, tailWord_469080, baseEnd_469080] using wordTrace_append hprefix tailTrace_469080
  have hstable : (prefixWord ++ tailWord_469080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469080).length < 2 ^ (prefixWord ++ tailWord_469080).sum := by decide
  have hdescent : baseEnd_469080 < baseStart_469080 := by decide
  rcases family_descends (prefixWord ++ tailWord_469080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469093 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_469093 : Nat := 118140960795 + 469093 * 2 ^ 59
def prefixEnd_469093 : Nat := 4983230072969 + 3 ^ 40 * 469093 * 2
def baseEnd_469093 : Nat := 160580120439758936786791

theorem tailTrace_469093 : CollatzResearch.WordTrace tailWord_469093 prefixEnd_469093 160580120439758936786791 := by
  unfold tailWord_469093
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109227289563650551251933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11406151526375767034167955 17109227289563650551251933)
  ·
    refine ⟨6415960233586368956719475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17109227289563650551251933 6415960233586368956719475)
    ·
      refine ⟨9623940350379553435079213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415960233586368956719475 9623940350379553435079213)
      ·
        refine ⟨3608977631392332538154705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9623940350379553435079213 3608977631392332538154705)
        ·
          refine ⟨2706733223544249403616029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608977631392332538154705 2706733223544249403616029)
          ·
            refine ⟨1015024958829093526356011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2706733223544249403616029 1015024958829093526356011)
            ·
              refine ⟨1522537438243640289534017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015024958829093526356011 1522537438243640289534017)
              ·
                refine ⟨1141903078682730217150513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522537438243640289534017 1141903078682730217150513)
                ·
                  refine ⟨856427309012047662862885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141903078682730217150513 856427309012047662862885)
                  ·
                    refine ⟨160580120439758936786791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 856427309012047662862885 160580120439758936786791)
                    ·
                      rfl

theorem cell22_469093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_469093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469093 prefixEnd_469093 := by exact prefixLift 469093
  have htrace : WordTrace (prefixWord ++ tailWord_469093) baseStart_469093 baseEnd_469093 := by
    simpa [prefixWord, tailWord_469093, baseEnd_469093] using wordTrace_append hprefix tailTrace_469093
  have hstable : (prefixWord ++ tailWord_469093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469093).length < 2 ^ (prefixWord ++ tailWord_469093).sum := by decide
  have hdescent : baseEnd_469093 < baseStart_469093 := by decide
  rcases family_descends (prefixWord ++ tailWord_469093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469142 : List Nat := [5, 3, 2, 1, 11]
def baseStart_469142 : Nat := 118140960795 + 469142 * 2 ^ 59
def prefixEnd_469142 : Nat := 4983230072969 + 3 ^ 40 * 469142 * 2
def baseEnd_469142 : Nat := 660892568482054083587

theorem tailTrace_469142 : CollatzResearch.WordTrace tailWord_469142 prefixEnd_469142 660892568482054083587 := by
  unfold tailWord_469142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069438404149133244986605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11407342977590754613190453 1069438404149133244986605)
  ·
    refine ⟨401039401555924966869977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1069438404149133244986605 401039401555924966869977)
    ·
      refine ⟨300779551166943725152483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401039401555924966869977 300779551166943725152483)
      ·
        refine ⟨451169326750415587728725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300779551166943725152483 451169326750415587728725)
        ·
          refine ⟨660892568482054083587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 451169326750415587728725 660892568482054083587)
          ·
            rfl

theorem cell22_469142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 11].length) (baseStart_469142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469142 prefixEnd_469142 := by exact prefixLift 469142
  have htrace : WordTrace (prefixWord ++ tailWord_469142) baseStart_469142 baseEnd_469142 := by
    simpa [prefixWord, tailWord_469142, baseEnd_469142] using wordTrace_append hprefix tailTrace_469142
  have hstable : (prefixWord ++ tailWord_469142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469142).length < 2 ^ (prefixWord ++ tailWord_469142).sum := by decide
  have hdescent : baseEnd_469142 < baseStart_469142 := by decide
  rcases family_descends (prefixWord ++ tailWord_469142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469153 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 5]
def baseStart_469153 : Nat := 118140960795 + 469153 * 2 ^ 59
def prefixEnd_469153 : Nat := 4983230072969 + 3 ^ 40 * 469153 * 2
def baseEnd_469153 : Nat := 53533553221979593428869

theorem tailTrace_469153 : CollatzResearch.WordTrace tailWord_469153 prefixEnd_469153 53533553221979593428869 := by
  unfold tailWord_469153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111415669346280798436113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11407610446230853865624075 17111415669346280798436113)
  ·
    refine ⟨12833561752009710598827085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17111415669346280798436113 12833561752009710598827085)
    ·
      refine ⟨4812585657003641474560157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12833561752009710598827085 4812585657003641474560157)
      ·
        refine ⟨1804719621376365552960059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4812585657003641474560157 1804719621376365552960059)
        ·
          refine ⟨2707079432064548329440089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804719621376365552960059 2707079432064548329440089)
          ·
            refine ⟨2030309574048411247080067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707079432064548329440089 2030309574048411247080067)
            ·
              refine ⟨3045464361072616870620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030309574048411247080067 3045464361072616870620101)
              ·
                refine ⟨571024567701115663241269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3045464361072616870620101 571024567701115663241269)
                ·
                  refine ⟨53533553221979593428869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571024567701115663241269 53533553221979593428869)
                  ·
                    rfl

theorem cell22_469153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_469153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469153 prefixEnd_469153 := by exact prefixLift 469153
  have htrace : WordTrace (prefixWord ++ tailWord_469153) baseStart_469153 baseEnd_469153 := by
    simpa [prefixWord, tailWord_469153, baseEnd_469153] using wordTrace_append hprefix tailTrace_469153
  have hstable : (prefixWord ++ tailWord_469153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469153).length < 2 ^ (prefixWord ++ tailWord_469153).sum := by decide
  have hdescent : baseEnd_469153 < baseStart_469153 := by decide
  rcases family_descends (prefixWord ++ tailWord_469153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469183 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 1, 4]
def baseStart_469183 : Nat := 118140960795 + 469183 * 2 ^ 59
def prefixEnd_469183 : Nat := 4983230072969 + 3 ^ 40 * 469183 * 2
def baseEnd_469183 : Nat := 160610929279028702036515

theorem tailTrace_469183 : CollatzResearch.WordTrace tailWord_469183 prefixEnd_469183 160610929279028702036515 := by
  unfold tailWord_469183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112509859237595922028203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11408339906158397281352135 17112509859237595922028203)
  ·
    refine ⟨25668764788856393883042305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17112509859237595922028203 25668764788856393883042305)
    ·
      refine ⟨19251573591642295412281729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25668764788856393883042305 19251573591642295412281729)
      ·
        refine ⟨14438680193731721559211297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19251573591642295412281729 14438680193731721559211297)
        ·
          refine ⟨10829010145298791169408473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14438680193731721559211297 10829010145298791169408473)
          ·
            refine ⟨8121757608974093377056355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829010145298791169408473 8121757608974093377056355)
            ·
              refine ⟨12182636413461140065584533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121757608974093377056355 12182636413461140065584533)
              ·
                refine ⟨571061081880990940574275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12182636413461140065584533 571061081880990940574275)
                ·
                  refine ⟨856591622821486410861413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571061081880990940574275 856591622821486410861413)
                  ·
                    refine ⟨160610929279028702036515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 856591622821486410861413 160610929279028702036515)
                    ·
                      rfl

theorem cell22_469183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_469183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469183 prefixEnd_469183 := by exact prefixLift 469183
  have htrace : WordTrace (prefixWord ++ tailWord_469183) baseStart_469183 baseEnd_469183 := by
    simpa [prefixWord, tailWord_469183, baseEnd_469183] using wordTrace_append hprefix tailTrace_469183
  have hstable : (prefixWord ++ tailWord_469183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469183).length < 2 ^ (prefixWord ++ tailWord_469183).sum := by decide
  have hdescent : baseEnd_469183 < baseStart_469183 := by decide
  rcases family_descends (prefixWord ++ tailWord_469183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_469211 : Nat := 118140960795 + 469211 * 2 ^ 59
def prefixEnd_469211 : Nat := 4983230072969 + 3 ^ 40 * 469211 * 2
def baseEnd_469211 : Nat := 160620514251245962336429

theorem tailTrace_469211 : CollatzResearch.WordTrace tailWord_469211 prefixEnd_469211 160620514251245962336429 := by
  unfold tailWord_469211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113531103136156704047487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11409020735424104469364991 17113531103136156704047487)
  ·
    refine ⟨25670296654704235056071231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17113531103136156704047487 25670296654704235056071231)
    ·
      refine ⟨38505444982056352584106847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25670296654704235056071231 38505444982056352584106847)
      ·
        refine ⟨57758167473084528876160271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38505444982056352584106847 57758167473084528876160271)
        ·
          refine ⟨86637251209626793314240407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57758167473084528876160271 86637251209626793314240407)
          ·
            refine ⟨129955876814440189971360611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86637251209626793314240407 129955876814440189971360611)
            ·
              refine ⟨194933815221660284957040917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129955876814440189971360611 194933815221660284957040917)
              ·
                refine ⟨9137522588515325857361293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194933815221660284957040917 9137522588515325857361293)
                ·
                  refine ⟨3426570970693247196510485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9137522588515325857361293 3426570970693247196510485)
                  ·
                    refine ⟨160620514251245962336429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3426570970693247196510485 160620514251245962336429)
                    ·
                      rfl

theorem cell22_469211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_469211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469211 prefixEnd_469211 := by exact prefixLift 469211
  have htrace : WordTrace (prefixWord ++ tailWord_469211) baseStart_469211 baseEnd_469211 := by
    simpa [prefixWord, tailWord_469211, baseEnd_469211] using wordTrace_append hprefix tailTrace_469211
  have hstable : (prefixWord ++ tailWord_469211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469211).length < 2 ^ (prefixWord ++ tailWord_469211).sum := by decide
  have hdescent : baseEnd_469211 < baseStart_469211 := by decide
  rcases family_descends (prefixWord ++ tailWord_469211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469275 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 3, 3]
def baseStart_469275 : Nat := 118140960795 + 469275 * 2 ^ 59
def prefixEnd_469275 : Nat := 4983230072969 + 3 ^ 40 * 469275 * 2
def baseEnd_469275 : Nat := 160642422759171128736233

theorem tailTrace_469275 : CollatzResearch.WordTrace tailWord_469275 prefixEnd_469275 160642422759171128736233 := by
  unfold tailWord_469275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17115865374904295634377279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11410576916602863756251519 17115865374904295634377279)
  ·
    refine ⟨25673798062356443451565919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17115865374904295634377279 25673798062356443451565919)
    ·
      refine ⟨38510697093534665177348879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25673798062356443451565919 38510697093534665177348879)
      ·
        refine ⟨57766045640301997766023319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38510697093534665177348879 57766045640301997766023319)
        ·
          refine ⟨86649068460452996649034979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57766045640301997766023319 86649068460452996649034979)
          ·
            refine ⟨129973602690679494973552469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649068460452996649034979 129973602690679494973552469)
            ·
              refine ⟨761564078265700165860659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 129973602690679494973552469 761564078265700165860659)
              ·
                refine ⟨1142346117398550248790989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761564078265700165860659 1142346117398550248790989)
                ·
                  refine ⟨428379794024456343296621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142346117398550248790989 428379794024456343296621)
                  ·
                    refine ⟨160642422759171128736233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428379794024456343296621 160642422759171128736233)
                    ·
                      rfl

theorem cell22_469275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].length) (baseStart_469275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469275 prefixEnd_469275 := by exact prefixLift 469275
  have htrace : WordTrace (prefixWord ++ tailWord_469275) baseStart_469275 baseEnd_469275 := by
    simpa [prefixWord, tailWord_469275, baseEnd_469275] using wordTrace_append hprefix tailTrace_469275
  have hstable : (prefixWord ++ tailWord_469275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469275).length < 2 ^ (prefixWord ++ tailWord_469275).sum := by decide
  have hdescent : baseEnd_469275 < baseStart_469275 := by decide
  rcases family_descends (prefixWord ++ tailWord_469275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469363 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_469363 : Nat := 118140960795 + 469363 * 2 ^ 59
def prefixEnd_469363 : Nat := 4983230072969 + 3 ^ 40 * 469363 * 2
def baseEnd_469363 : Nat := 160672546957568232535963

theorem tailTrace_469363 : CollatzResearch.WordTrace tailWord_469363 prefixEnd_469363 160672546957568232535963 := by
  unfold tailWord_469363
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119074998585486663580743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11412716665723657775720495 17119074998585486663580743)
  ·
    refine ⟨25678612497878229995371115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119074998585486663580743 25678612497878229995371115)
    ·
      refine ⟨38517918746817344993056673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678612497878229995371115 38517918746817344993056673)
      ·
        refine ⟨28888439060113008744792505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38517918746817344993056673 28888439060113008744792505)
        ·
          refine ⟨21666329295084756558594379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28888439060113008744792505 21666329295084756558594379)
          ·
            refine ⟨32499493942627134837891569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21666329295084756558594379 32499493942627134837891569)
            ·
              refine ⟨24374620456970351128418677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32499493942627134837891569 24374620456970351128418677)
              ·
                refine ⟨2285120667840970418289251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24374620456970351128418677 2285120667840970418289251)
                ·
                  refine ⟨3427681001761455627433877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285120667840970418289251 3427681001761455627433877)
                  ·
                    refine ⟨160672546957568232535963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3427681001761455627433877 160672546957568232535963)
                    ·
                      rfl

theorem cell22_469363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_469363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469363 prefixEnd_469363 := by exact prefixLift 469363
  have htrace : WordTrace (prefixWord ++ tailWord_469363) baseStart_469363 baseEnd_469363 := by
    simpa [prefixWord, tailWord_469363, baseEnd_469363] using wordTrace_append hprefix tailTrace_469363
  have hstable : (prefixWord ++ tailWord_469363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469363).length < 2 ^ (prefixWord ++ tailWord_469363).sum := by decide
  have hdescent : baseEnd_469363 < baseStart_469363 := by decide
  rcases family_descends (prefixWord ++ tailWord_469363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469380 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_469380 : Nat := 118140960795 + 469380 * 2 ^ 59
def prefixEnd_469380 : Nat := 4983230072969 + 3 ^ 40 * 469380 * 2
def baseEnd_469380 : Nat := 160678366404985854860911

theorem tailTrace_469380 : CollatzResearch.WordTrace tailWord_469380 prefixEnd_469380 160678366404985854860911 := by
  unfold tailWord_469380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559847519761949283474797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11413130026349265711299729 8559847519761949283474797)
  ·
    refine ⟨3209942819910730981303049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8559847519761949283474797 3209942819910730981303049)
    ·
      refine ⟨2407457114933048235977287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3209942819910730981303049 2407457114933048235977287)
      ·
        refine ⟨3611185672399572353965931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407457114933048235977287 3611185672399572353965931)
        ·
          refine ⟨5416778508599358530948897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611185672399572353965931 5416778508599358530948897)
          ·
            refine ⟨4062583881449518898211673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416778508599358530948897 4062583881449518898211673)
            ·
              refine ⟨3046937911087139173658755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062583881449518898211673 3046937911087139173658755)
              ·
                refine ⟨4570406866630708760488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046937911087139173658755 4570406866630708760488133)
                ·
                  refine ⟨856951287493257892591525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4570406866630708760488133 856951287493257892591525)
                  ·
                    refine ⟨160678366404985854860911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 856951287493257892591525 160678366404985854860911)
                    ·
                      rfl

theorem cell22_469380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_469380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469380 prefixEnd_469380 := by exact prefixLift 469380
  have htrace : WordTrace (prefixWord ++ tailWord_469380) baseStart_469380 baseEnd_469380 := by
    simpa [prefixWord, tailWord_469380, baseEnd_469380] using wordTrace_append hprefix tailTrace_469380
  have hstable : (prefixWord ++ tailWord_469380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469380).length < 2 ^ (prefixWord ++ tailWord_469380).sum := by decide
  have hdescent : baseEnd_469380 < baseStart_469380 := by decide
  rcases family_descends (prefixWord ++ tailWord_469380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_469393 : Nat := 118140960795 + 469393 * 2 ^ 59
def prefixEnd_469393 : Nat := 4983230072969 + 3 ^ 40 * 469393 * 2
def baseEnd_469393 : Nat := 160682816570658154285871

theorem tailTrace_469393 : CollatzResearch.WordTrace tailWord_469393 prefixEnd_469393 160682816570658154285871 := by
  unfold tailWord_469393
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120169188476801787172833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11413446125651201191448555 17120169188476801787172833)
  ·
    refine ⟨12840126891357601340379625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17120169188476801787172833 12840126891357601340379625)
    ·
      refine ⟨9630095168518201005284719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12840126891357601340379625 9630095168518201005284719)
      ·
        refine ⟨14445142752777301507927079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630095168518201005284719 14445142752777301507927079)
        ·
          refine ⟨21667714129165952261890619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14445142752777301507927079 21667714129165952261890619)
          ·
            refine ⟨32501571193748928392835929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21667714129165952261890619 32501571193748928392835929)
            ·
              refine ⟨24376178395311696294626947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32501571193748928392835929 24376178395311696294626947)
              ·
                refine ⟨36564267592967544441940421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24376178395311696294626947 36564267592967544441940421)
                ·
                  refine ⟨6855800173681414582863829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36564267592967544441940421 6855800173681414582863829)
                  ·
                    refine ⟨160682816570658154285871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6855800173681414582863829 160682816570658154285871)
                    ·
                      rfl

theorem cell22_469393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_469393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469393 prefixEnd_469393 := by exact prefixLift 469393
  have htrace : WordTrace (prefixWord ++ tailWord_469393) baseStart_469393 baseEnd_469393 := by
    simpa [prefixWord, tailWord_469393, baseEnd_469393] using wordTrace_append hprefix tailTrace_469393
  have hstable : (prefixWord ++ tailWord_469393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469393).length < 2 ^ (prefixWord ++ tailWord_469393).sum := by decide
  have hdescent : baseEnd_469393 < baseStart_469393 := by decide
  rcases family_descends (prefixWord ++ tailWord_469393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469410 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_469410 : Nat := 118140960795 + 469410 * 2 ^ 59
def prefixEnd_469410 : Nat := 4983230072969 + 3 ^ 40 * 469410 * 2
def baseEnd_469410 : Nat := 160688636018075776610819

theorem tailTrace_469410 : CollatzResearch.WordTrace tailWord_469410 prefixEnd_469410 160688636018075776610819 := by
  unfold tailWord_469410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280197307353803422635421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11413859486276809127027789 4280197307353803422635421)
  ·
    refine ⟨1605073990257676283488283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4280197307353803422635421 1605073990257676283488283)
    ·
      refine ⟨2407610985386514425232425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605073990257676283488283 2407610985386514425232425)
      ·
        refine ⟨1805708239039885818924319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2407610985386514425232425 1805708239039885818924319)
        ·
          refine ⟨2708562358559828728386479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805708239039885818924319 2708562358559828728386479)
          ·
            refine ⟨4062843537839743092579719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708562358559828728386479 4062843537839743092579719)
            ·
              refine ⟨6094265306759614638869579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062843537839743092579719 6094265306759614638869579)
              ·
                refine ⟨9141397960139421958304369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094265306759614638869579 9141397960139421958304369)
                ·
                  refine ⟨6856048470104566468728277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141397960139421958304369 6856048470104566468728277)
                  ·
                    refine ⟨160688636018075776610819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6856048470104566468728277 160688636018075776610819)
                    ·
                      rfl

theorem cell22_469410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_469410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469410 prefixEnd_469410 := by exact prefixLift 469410
  have htrace : WordTrace (prefixWord ++ tailWord_469410) baseStart_469410 baseEnd_469410 := by
    simpa [prefixWord, tailWord_469410, baseEnd_469410] using wordTrace_append hprefix tailTrace_469410
  have hstable : (prefixWord ++ tailWord_469410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469410).length < 2 ^ (prefixWord ++ tailWord_469410).sum := by decide
  have hdescent : baseEnd_469410 < baseStart_469410 := by decide
  rcases family_descends (prefixWord ++ tailWord_469410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469440 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_469440 : Nat := 118140960795 + 469440 * 2 ^ 59
def prefixEnd_469440 : Nat := 4983230072969 + 3 ^ 40 * 469440 * 2
def baseEnd_469440 : Nat := 53566301877055232786909

theorem tailTrace_469440 : CollatzResearch.WordTrace tailWord_469440 prefixEnd_469440 53566301877055232786909 := by
  unfold tailWord_469440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560941709653264407066887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11414588946204352542755849 8560941709653264407066887)
  ·
    refine ⟨12841412564479896610600331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8560941709653264407066887 12841412564479896610600331)
    ·
      refine ⟨19262118846719844915900497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841412564479896610600331 19262118846719844915900497)
      ·
        refine ⟨14446589135039883686925373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19262118846719844915900497 14446589135039883686925373)
        ·
          refine ⟨5417470925639956382597015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14446589135039883686925373 5417470925639956382597015)
          ·
            refine ⟨8126206388459934573895523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417470925639956382597015 8126206388459934573895523)
            ·
              refine ⟨12189309582689901860843285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126206388459934573895523 12189309582689901860843285)
              ·
                refine ⟨571373886688589149727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12189309582689901860843285 571373886688589149727029)
                ·
                  refine ⟨53566301877055232786909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571373886688589149727029 53566301877055232786909)
                  ·
                    rfl

theorem cell22_469440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_469440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469440 prefixEnd_469440 := by exact prefixLift 469440
  have htrace : WordTrace (prefixWord ++ tailWord_469440) baseStart_469440 baseEnd_469440 := by
    simpa [prefixWord, tailWord_469440, baseEnd_469440] using wordTrace_append hprefix tailTrace_469440
  have hstable : (prefixWord ++ tailWord_469440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469440).length < 2 ^ (prefixWord ++ tailWord_469440).sum := by decide
  have hdescent : baseEnd_469440 < baseStart_469440 := by decide
  rcases family_descends (prefixWord ++ tailWord_469440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469500 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_469500 : Nat := 118140960795 + 469500 * 2 ^ 59
def prefixEnd_469500 : Nat := 4983230072969 + 3 ^ 40 * 469500 * 2
def baseEnd_469500 : Nat := 160719444857345541860543

theorem tailTrace_469500 : CollatzResearch.WordTrace tailWord_469500 prefixEnd_469500 160719444857345541860543 := by
  unfold tailWord_469500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562035899544579530658977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11416047866059439374211969 8562035899544579530658977)
  ·
    refine ⟨6421526924658434647994233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562035899544579530658977 6421526924658434647994233)
    ·
      refine ⟨4816145193493825985995675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6421526924658434647994233 4816145193493825985995675)
      ·
        refine ⟨7224217790240738978993513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816145193493825985995675 7224217790240738978993513)
        ·
          refine ⟨5418163342680554234245135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7224217790240738978993513 5418163342680554234245135)
          ·
            refine ⟨8127245014020831351367703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418163342680554234245135 8127245014020831351367703)
            ·
              refine ⟨12190867521031247027051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127245014020831351367703 12190867521031247027051555)
              ·
                refine ⟨18286301281546870540577333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190867521031247027051555 18286301281546870540577333)
                ·
                  refine ⟨1714340745145019113179125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18286301281546870540577333 1714340745145019113179125)
                  ·
                    refine ⟨160719444857345541860543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1714340745145019113179125 160719444857345541860543)
                    ·
                      rfl

theorem cell22_469500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_469500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469500 prefixEnd_469500 := by exact prefixLift 469500
  have htrace : WordTrace (prefixWord ++ tailWord_469500) baseStart_469500 baseEnd_469500 := by
    simpa [prefixWord, tailWord_469500, baseEnd_469500] using wordTrace_append hprefix tailTrace_469500
  have hstable : (prefixWord ++ tailWord_469500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469500).length < 2 ^ (prefixWord ++ tailWord_469500).sum := by decide
  have hdescent : baseEnd_469500 < baseStart_469500 := by decide
  rcases family_descends (prefixWord ++ tailWord_469500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469530 : List Nat := [3, 1, 1, 3, 1, 1, 2, 10]
def baseStart_469530 : Nat := 118140960795 + 469530 * 2 ^ 59
def prefixEnd_469530 : Nat := 4983230072969 + 3 ^ 40 * 469530 * 2
def baseEnd_469530 : Nat := 17858857163381718178939

theorem tailTrace_469530 : CollatzResearch.WordTrace tailWord_469530 prefixEnd_469530 17858857163381718178939 := by
  unfold tailWord_469530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281291497245118546227511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11416777325986982789940029 4281291497245118546227511)
  ·
    refine ⟨6421937245867677819341267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4281291497245118546227511 6421937245867677819341267)
    ·
      refine ⟨9632905868801516729011901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421937245867677819341267 9632905868801516729011901)
      ·
        refine ⟨3612339700800568773379463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9632905868801516729011901 3612339700800568773379463)
        ·
          refine ⟨5418509551200853160069195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612339700800568773379463 5418509551200853160069195)
          ·
            refine ⟨8127764326801279740103793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418509551200853160069195 8127764326801279740103793)
            ·
              refine ⟨6095823245100959805077845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8127764326801279740103793 6095823245100959805077845)
              ·
                refine ⟨17858857163381718178939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6095823245100959805077845 17858857163381718178939)
                ·
                  rfl

theorem cell22_469530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_469530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469530 prefixEnd_469530 := by exact prefixLift 469530
  have htrace : WordTrace (prefixWord ++ tailWord_469530) baseStart_469530 baseEnd_469530 := by
    simpa [prefixWord, tailWord_469530, baseEnd_469530] using wordTrace_append hprefix tailTrace_469530
  have hstable : (prefixWord ++ tailWord_469530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469530).length < 2 ^ (prefixWord ++ tailWord_469530).sum := by decide
  have hdescent : baseEnd_469530 < baseStart_469530 := by decide
  rcases family_descends (prefixWord ++ tailWord_469530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469532 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_469532 : Nat := 118140960795 + 469532 * 2 ^ 59
def prefixEnd_469532 : Nat := 4983230072969 + 3 ^ 40 * 469532 * 2
def baseEnd_469532 : Nat := 160730399111308125060445

theorem tailTrace_469532 : CollatzResearch.WordTrace tailWord_469532 prefixEnd_469532 160730399111308125060445 := by
  unfold tailWord_469532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562619467486614263241425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11416825956648819017655233 8562619467486614263241425)
  ·
    refine ⟨6421964600614960697431069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562619467486614263241425 6421964600614960697431069)
    ·
      refine ⟨2408236725230610261536651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6421964600614960697431069 2408236725230610261536651)
      ·
        refine ⟨3612355087845915392304977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408236725230610261536651 3612355087845915392304977)
        ·
          refine ⟨2709266315884436544228733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612355087845915392304977 2709266315884436544228733)
          ·
            refine ⟨1015974868456663704085775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2709266315884436544228733 1015974868456663704085775)
            ·
              refine ⟨1523962302684995556128663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015974868456663704085775 1523962302684995556128663)
              ·
                refine ⟨2285943454027493334192995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523962302684995556128663 2285943454027493334192995)
                ·
                  refine ⟨3428915181041240001289493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285943454027493334192995 3428915181041240001289493)
                  ·
                    refine ⟨160730399111308125060445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3428915181041240001289493 160730399111308125060445)
                    ·
                      rfl

theorem cell22_469532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_469532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469532 prefixEnd_469532 := by exact prefixLift 469532
  have htrace : WordTrace (prefixWord ++ tailWord_469532) baseStart_469532 baseEnd_469532 := by
    simpa [prefixWord, tailWord_469532, baseEnd_469532] using wordTrace_append hprefix tailTrace_469532
  have hstable : (prefixWord ++ tailWord_469532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469532).length < 2 ^ (prefixWord ++ tailWord_469532).sum := by decide
  have hdescent : baseEnd_469532 < baseStart_469532 := by decide
  rcases family_descends (prefixWord ++ tailWord_469532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469536 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_469536 : Nat := 118140960795 + 469536 * 2 ^ 59
def prefixEnd_469536 : Nat := 4983230072969 + 3 ^ 40 * 469536 * 2
def baseEnd_469536 : Nat := 53577256131017815986811

theorem tailTrace_469536 : CollatzResearch.WordTrace tailWord_469536 prefixEnd_469536 53577256131017815986811 := by
  unfold tailWord_469536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562692413479368604814231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11416923217972491473085641 8562692413479368604814231)
  ·
    refine ⟨12844038620219052907221347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8562692413479368604814231 12844038620219052907221347)
    ·
      refine ⟨19266057930328579360832021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12844038620219052907221347 19266057930328579360832021)
      ·
        refine ⟨903096465484152157539001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19266057930328579360832021 903096465484152157539001)
        ·
          refine ⟨677322349113114118154251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903096465484152157539001 677322349113114118154251)
          ·
            refine ⟨1015983523669671177231377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677322349113114118154251 1015983523669671177231377)
            ·
              refine ⟨761987642752253382923533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015983523669671177231377 761987642752253382923533)
              ·
                refine ⟨285745366032095018596325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761987642752253382923533 285745366032095018596325)
                ·
                  refine ⟨53577256131017815986811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285745366032095018596325 53577256131017815986811)
                  ·
                    rfl

theorem cell22_469536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_469536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469536 prefixEnd_469536 := by exact prefixLift 469536
  have htrace : WordTrace (prefixWord ++ tailWord_469536) baseStart_469536 baseEnd_469536 := by
    simpa [prefixWord, tailWord_469536, baseEnd_469536] using wordTrace_append hprefix tailTrace_469536
  have hstable : (prefixWord ++ tailWord_469536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469536).length < 2 ^ (prefixWord ++ tailWord_469536).sum := by decide
  have hdescent : baseEnd_469536 < baseStart_469536 := by decide
  rcases family_descends (prefixWord ++ tailWord_469536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469581 : List Nat := [1, 6, 1, 1, 2, 3, 2, 6]
def baseStart_469581 : Nat := 118140960795 + 469581 * 2 ^ 59
def prefixEnd_469581 : Nat := 4983230072969 + 3 ^ 40 * 469581 * 2
def baseEnd_469581 : Nat := 17860796979187592287255

theorem tailTrace_469581 : CollatzResearch.WordTrace tailWord_469581 prefixEnd_469581 17860796979187592287255 := by
  unfold tailWord_469581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127026111795709895016597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418017407863806596677731 17127026111795709895016597)
  ·
    refine ⟨802829348990423901328903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17127026111795709895016597 802829348990423901328903)
    ·
      refine ⟨1204244023485635851993355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802829348990423901328903 1204244023485635851993355)
      ·
        refine ⟨1806366035228453777990033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204244023485635851993355 1806366035228453777990033)
        ·
          refine ⟨1354774526421340333492525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806366035228453777990033 1354774526421340333492525)
          ·
            refine ⟨508040447408002625059697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1354774526421340333492525 508040447408002625059697)
            ·
              refine ⟨381030335556001968794773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508040447408002625059697 381030335556001968794773)
              ·
                refine ⟨17860796979187592287255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381030335556001968794773 17860796979187592287255)
                ·
                  rfl

theorem cell22_469581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 6].length) (baseStart_469581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469581 prefixEnd_469581 := by exact prefixLift 469581
  have htrace : WordTrace (prefixWord ++ tailWord_469581) baseStart_469581 baseEnd_469581 := by
    simpa [prefixWord, tailWord_469581, baseEnd_469581] using wordTrace_append hprefix tailTrace_469581
  have hstable : (prefixWord ++ tailWord_469581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469581).length < 2 ^ (prefixWord ++ tailWord_469581).sum := by decide
  have hdescent : baseEnd_469581 < baseStart_469581 := by decide
  rcases family_descends (prefixWord ++ tailWord_469581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469598 : List Nat := [4, 4, 1, 2, 1, 2, 8]
def baseStart_469598 : Nat := 118140960795 + 469598 * 2 ^ 59
def prefixEnd_469598 : Nat := 4983230072969 + 3 ^ 40 * 469598 * 2
def baseEnd_469598 : Nat := 5953814528152072330009

theorem tailTrace_469598 : CollatzResearch.WordTrace tailWord_469598 prefixEnd_469598 5953814528152072330009 := by
  unfold tailWord_469598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140955769091765224798181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11418430768489414532256965 2140955769091765224798181)
  ·
    refine ⟨401429206704705979649659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2140955769091765224798181 401429206704705979649659)
    ·
      refine ⟨602143810057058969474489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401429206704705979649659 602143810057058969474489)
      ·
        refine ⟨451607857542794227105867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602143810057058969474489 451607857542794227105867)
        ·
          refine ⟨677411786314191340658801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451607857542794227105867 677411786314191340658801)
          ·
            refine ⟨508058839735643505494101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677411786314191340658801 508058839735643505494101)
            ·
              refine ⟨5953814528152072330009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 508058839735643505494101 5953814528152072330009)
              ·
                rfl

theorem cell22_469598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 8].length) (baseStart_469598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469598 prefixEnd_469598 := by exact prefixLift 469598
  have htrace : WordTrace (prefixWord ++ tailWord_469598) baseStart_469598 baseEnd_469598 := by
    simpa [prefixWord, tailWord_469598, baseEnd_469598] using wordTrace_append hprefix tailTrace_469598
  have hstable : (prefixWord ++ tailWord_469598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469598).length < 2 ^ (prefixWord ++ tailWord_469598).sum := by decide
  have hdescent : baseEnd_469598 < baseStart_469598 := by decide
  rcases family_descends (prefixWord ++ tailWord_469598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469656 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_469656 : Nat := 118140960795 + 469656 * 2 ^ 59
def prefixEnd_469656 : Nat := 4983230072969 + 3 ^ 40 * 469656 * 2
def baseEnd_469656 : Nat := 160772846845413134960065

theorem tailTrace_469656 : CollatzResearch.WordTrace tailWord_469656 prefixEnd_469656 160772846845413134960065 := by
  unfold tailWord_469656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564880793261998851998411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11419841057682665135997881 8564880793261998851998411)
  ·
    refine ⟨12847321189892998277997617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8564880793261998851998411 12847321189892998277997617)
    ·
      refine ⟨9635490892419748708498213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12847321189892998277997617 9635490892419748708498213)
      ·
        refine ⟨1806654542328702882843415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9635490892419748708498213 1806654542328702882843415)
        ·
          refine ⟨2709981813493054324265123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806654542328702882843415 2709981813493054324265123)
          ·
            refine ⟨4064972720239581486397685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709981813493054324265123 4064972720239581486397685)
            ·
              refine ⟨381091192522460764349783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4064972720239581486397685 381091192522460764349783)
              ·
                refine ⟨571636788783691146524675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381091192522460764349783 571636788783691146524675)
                ·
                  refine ⟨857455183175536719787013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571636788783691146524675 857455183175536719787013)
                  ·
                    refine ⟨160772846845413134960065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857455183175536719787013 160772846845413134960065)
                    ·
                      rfl

theorem cell22_469656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_469656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469656 prefixEnd_469656 := by exact prefixLift 469656
  have htrace : WordTrace (prefixWord ++ tailWord_469656) baseStart_469656 baseEnd_469656 := by
    simpa [prefixWord, tailWord_469656, baseEnd_469656] using wordTrace_append hprefix tailTrace_469656
  have hstable : (prefixWord ++ tailWord_469656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469656).length < 2 ^ (prefixWord ++ tailWord_469656).sum := by decide
  have hdescent : baseEnd_469656 < baseStart_469656 := by decide
  rcases family_descends (prefixWord ++ tailWord_469656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_469667 : Nat := 118140960795 + 469667 * 2 ^ 59
def prefixEnd_469667 : Nat := 4983230072969 + 3 ^ 40 * 469667 * 2
def baseEnd_469667 : Nat := 160776612370212772935031

theorem tailTrace_469667 : CollatzResearch.WordTrace tailWord_469667 prefixEnd_469667 160776612370212772935031 := by
  unfold tailWord_469667
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130162789484146582647255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11420108526322764388431503 17130162789484146582647255)
  ·
    refine ⟨25695244184226219873970883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17130162789484146582647255 25695244184226219873970883)
    ·
      refine ⟨38542866276339329810956325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695244184226219873970883 38542866276339329810956325)
      ·
        refine ⟨7226787426813624339554311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38542866276339329810956325 7226787426813624339554311)
        ·
          refine ⟨10840181140220436509331467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226787426813624339554311 10840181140220436509331467)
          ·
            refine ⟨16260271710330654763997201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840181140220436509331467 16260271710330654763997201)
            ·
              refine ⟨12195203782747991072997901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16260271710330654763997201 12195203782747991072997901)
              ·
                refine ⟨4573201418530496652374213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12195203782747991072997901 4573201418530496652374213)
                ·
                  refine ⟨857475265974468122320165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4573201418530496652374213 857475265974468122320165)
                  ·
                    refine ⟨160776612370212772935031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857475265974468122320165 160776612370212772935031)
                    ·
                      rfl

theorem cell22_469667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_469667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469667 prefixEnd_469667 := by exact prefixLift 469667
  have htrace : WordTrace (prefixWord ++ tailWord_469667) baseStart_469667 baseEnd_469667 := by
    simpa [prefixWord, tailWord_469667, baseEnd_469667] using wordTrace_append hprefix tailTrace_469667
  have hstable : (prefixWord ++ tailWord_469667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469667).length < 2 ^ (prefixWord ++ tailWord_469667).sum := by decide
  have hdescent : baseEnd_469667 < baseStart_469667 := by decide
  rcases family_descends (prefixWord ++ tailWord_469667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469731 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 3, 3]
def baseStart_469731 : Nat := 118140960795 + 469731 * 2 ^ 59
def prefixEnd_469731 : Nat := 4983230072969 + 3 ^ 40 * 469731 * 2
def baseEnd_469731 : Nat := 160798520878137939334835

theorem tailTrace_469731 : CollatzResearch.WordTrace tailWord_469731 prefixEnd_469731 160798520878137939334835 := by
  unfold tailWord_469731
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132497061252285512977047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11421664707501523675318031 17132497061252285512977047)
  ·
    refine ⟨25698745591878428269465571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17132497061252285512977047 25698745591878428269465571)
    ·
      refine ⟨38548118387817642404198357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25698745591878428269465571 38548118387817642404198357)
      ·
        refine ⟨903471524714475993848399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 38548118387817642404198357 903471524714475993848399)
        ·
          refine ⟨1355207287071713990772599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903471524714475993848399 1355207287071713990772599)
          ·
            refine ⟨2032810930607570986158899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355207287071713990772599 2032810930607570986158899)
            ·
              refine ⟨3049216395911356479238349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032810930607570986158899 3049216395911356479238349)
              ·
                refine ⟨1143456148466758679714381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049216395911356479238349 1143456148466758679714381)
                ·
                  refine ⟨428796055675034504892893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143456148466758679714381 428796055675034504892893)
                  ·
                    refine ⟨160798520878137939334835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428796055675034504892893 160798520878137939334835)
                    ·
                      rfl

theorem cell22_469731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].length) (baseStart_469731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469731 prefixEnd_469731 := by exact prefixLift 469731
  have htrace : WordTrace (prefixWord ++ tailWord_469731) baseStart_469731 baseEnd_469731 := by
    simpa [prefixWord, tailWord_469731, baseEnd_469731] using wordTrace_append hprefix tailTrace_469731
  have hstable : (prefixWord ++ tailWord_469731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469731).length < 2 ^ (prefixWord ++ tailWord_469731).sum := by decide
  have hdescent : baseEnd_469731 < baseStart_469731 := by decide
  rcases family_descends (prefixWord ++ tailWord_469731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_469774 : Nat := 118140960795 + 469774 * 2 ^ 59
def prefixEnd_469774 : Nat := 4983230072969 + 3 ^ 40 * 469774 * 2
def baseEnd_469774 : Nat := 160813240656900160509703

theorem tailTrace_469774 : CollatzResearch.WordTrace tailWord_469774 prefixEnd_469774 160813240656900160509703 := by
  unfold tailWord_469774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141758175012062982099047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11422710266731002571194917 2141758175012062982099047)
  ·
    refine ⟨3212637262518094473148571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141758175012062982099047 3212637262518094473148571)
    ·
      refine ⟨4818955893777141709722857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3212637262518094473148571 4818955893777141709722857)
      ·
        refine ⟨3614216920332856282292143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4818955893777141709722857 3614216920332856282292143)
        ·
          refine ⟨5421325380499284423438215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614216920332856282292143 5421325380499284423438215)
          ·
            refine ⟨8131988070748926635157323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421325380499284423438215 8131988070748926635157323)
            ·
              refine ⟨12197982106123389952735985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131988070748926635157323 12197982106123389952735985)
              ·
                refine ⟨9148486579592542464551989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12197982106123389952735985 9148486579592542464551989)
                ·
                  refine ⟨857670616836800856051749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9148486579592542464551989 857670616836800856051749)
                  ·
                    refine ⟨160813240656900160509703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857670616836800856051749 160813240656900160509703)
                    ·
                      rfl

theorem cell22_469774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_469774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469774 prefixEnd_469774 := by exact prefixLift 469774
  have htrace : WordTrace (prefixWord ++ tailWord_469774) baseStart_469774 baseEnd_469774 := by
    simpa [prefixWord, tailWord_469774, baseEnd_469774] using wordTrace_append hprefix tailTrace_469774
  have hstable : (prefixWord ++ tailWord_469774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469774).length < 2 ^ (prefixWord ++ tailWord_469774).sum := by decide
  have hdescent : baseEnd_469774 < baseStart_469774 := by decide
  rcases family_descends (prefixWord ++ tailWord_469774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469787 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_469787 : Nat := 118140960795 + 469787 * 2 ^ 59
def prefixEnd_469787 : Nat := 4983230072969 + 3 ^ 40 * 469787 * 2
def baseEnd_469787 : Nat := 160817690822572459934663

theorem tailTrace_469787 : CollatzResearch.WordTrace tailWord_469787 prefixEnd_469787 160817690822572459934663 := by
  unfold tailWord_469787
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134539549049407077015615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11423026366032938051343743 17134539549049407077015615)
  ·
    refine ⟨25701809323574110615523423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134539549049407077015615 25701809323574110615523423)
    ·
      refine ⟨38552713985361165923285135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25701809323574110615523423 38552713985361165923285135)
      ·
        refine ⟨57829070978041748884927703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38552713985361165923285135 57829070978041748884927703)
        ·
          refine ⟨86743606467062623327391555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57829070978041748884927703 86743606467062623327391555)
          ·
            refine ⟨130115409700593934991087333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86743606467062623327391555 130115409700593934991087333)
            ·
              refine ⟨24396639318861362810828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130115409700593934991087333 24396639318861362810828875)
              ·
                refine ⟨36594958978292044216243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24396639318861362810828875 36594958978292044216243313)
                ·
                  refine ⟨27446219233719033162182485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36594958978292044216243313 27446219233719033162182485)
                  ·
                    refine ⟨160817690822572459934663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27446219233719033162182485 160817690822572459934663)
                    ·
                      rfl

theorem cell22_469787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_469787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469787 prefixEnd_469787 := by exact prefixLift 469787
  have htrace : WordTrace (prefixWord ++ tailWord_469787) baseStart_469787 baseEnd_469787 := by
    simpa [prefixWord, tailWord_469787, baseEnd_469787] using wordTrace_append hprefix tailTrace_469787
  have hstable : (prefixWord ++ tailWord_469787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469787).length < 2 ^ (prefixWord ++ tailWord_469787).sum := by decide
  have hdescent : baseEnd_469787 < baseStart_469787 := by decide
  rcases family_descends (prefixWord ++ tailWord_469787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469804 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_469804 : Nat := 118140960795 + 469804 * 2 ^ 59
def prefixEnd_469804 : Nat := 4983230072969 + 3 ^ 40 * 469804 * 2
def baseEnd_469804 : Nat := 160823510269990082259611

theorem tailTrace_469804 : CollatzResearch.WordTrace tailWord_469804 prefixEnd_469804 160823510269990082259611 := by
  unfold tailWord_469804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567579794993909490192233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11423439726658545986922977 8567579794993909490192233)
  ·
    refine ⟨6425684846245432117644175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8567579794993909490192233 6425684846245432117644175)
    ·
      refine ⟨9638527269368148176466263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425684846245432117644175 9638527269368148176466263)
      ·
        refine ⟨14457790904052222264699395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638527269368148176466263 14457790904052222264699395)
        ·
          refine ⟨21686686356078333397049093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457790904052222264699395 21686686356078333397049093)
          ·
            refine ⟨4066253691764687511946705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21686686356078333397049093 4066253691764687511946705)
            ·
              refine ⟨3049690268823515633960029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066253691764687511946705 3049690268823515633960029)
              ·
                refine ⟨1143633850808818362735011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049690268823515633960029 1143633850808818362735011)
                ·
                  refine ⟨1715450776213227544102517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143633850808818362735011 1715450776213227544102517)
                  ·
                    refine ⟨160823510269990082259611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1715450776213227544102517 160823510269990082259611)
                    ·
                      rfl

theorem cell22_469804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_469804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469804 prefixEnd_469804 := by exact prefixLift 469804
  have htrace : WordTrace (prefixWord ++ tailWord_469804) baseStart_469804 baseEnd_469804 := by
    simpa [prefixWord, tailWord_469804, baseEnd_469804] using wordTrace_append hprefix tailTrace_469804
  have hstable : (prefixWord ++ tailWord_469804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469804).length < 2 ^ (prefixWord ++ tailWord_469804).sum := by decide
  have hdescent : baseEnd_469804 < baseStart_469804 := by decide
  rcases family_descends (prefixWord ++ tailWord_469804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469836 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_469836 : Nat := 118140960795 + 469836 * 2 ^ 59
def prefixEnd_469836 : Nat := 4983230072969 + 3 ^ 40 * 469836 * 2
def baseEnd_469836 : Nat := 160834464523952665459513

theorem tailTrace_469836 : CollatzResearch.WordTrace tailWord_469836 prefixEnd_469836 160834464523952665459513 := by
  unfold tailWord_469836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568163362935944222774681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11424217817247925630366241 8568163362935944222774681)
  ·
    refine ⟨6426122522201958167081011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8568163362935944222774681 6426122522201958167081011)
    ·
      refine ⟨9639183783302937250621517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426122522201958167081011 9639183783302937250621517)
      ·
        refine ⟨3614693918738601468983069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9639183783302937250621517 3614693918738601468983069)
        ·
          refine ⟨1355510219526975550868651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3614693918738601468983069 1355510219526975550868651)
          ·
            refine ⟨2033265329290463326302977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355510219526975550868651 2033265329290463326302977)
            ·
              refine ⟨1524948996967847494727233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033265329290463326302977 1524948996967847494727233)
              ·
                refine ⟨1143711747725885621045425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524948996967847494727233 1143711747725885621045425)
                ·
                  refine ⟨857783810794414215784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143711747725885621045425 857783810794414215784069)
                  ·
                    refine ⟨160834464523952665459513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857783810794414215784069 160834464523952665459513)
                    ·
                      rfl

theorem cell22_469836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_469836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469836 prefixEnd_469836 := by exact prefixLift 469836
  have htrace : WordTrace (prefixWord ++ tailWord_469836) baseStart_469836 baseEnd_469836 := by
    simpa [prefixWord, tailWord_469836, baseEnd_469836] using wordTrace_append hprefix tailTrace_469836
  have hstable : (prefixWord ++ tailWord_469836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469836).length < 2 ^ (prefixWord ++ tailWord_469836).sum := by decide
  have hdescent : baseEnd_469836 < baseStart_469836 := by decide
  rcases family_descends (prefixWord ++ tailWord_469836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469870 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_469870 : Nat := 118140960795 + 469870 * 2 ^ 59
def prefixEnd_469870 : Nat := 4983230072969 + 3 ^ 40 * 469870 * 2
def baseEnd_469870 : Nat := 160846103418787910109409

theorem tailTrace_469870 : CollatzResearch.WordTrace tailWord_469870 prefixEnd_469870 160846103418787910109409 := by
  unfold tailWord_469870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142195850968589031535883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11425044538499141501524709 2142195850968589031535883)
  ·
    refine ⟨3213293776452883547303825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142195850968589031535883 3213293776452883547303825)
    ·
      refine ⟨2409970332339662660477869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213293776452883547303825 2409970332339662660477869)
      ·
        refine ⟨903738874627373497679201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2409970332339662660477869 903738874627373497679201)
        ·
          refine ⟨677804155970530123259401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903738874627373497679201 677804155970530123259401)
          ·
            refine ⟨508353116977897592444551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677804155970530123259401 508353116977897592444551)
            ·
              refine ⟨762529675466846388666827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508353116977897592444551 762529675466846388666827)
              ·
                refine ⟨1143794513200269583000241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762529675466846388666827 1143794513200269583000241)
                ·
                  refine ⟨857845884900202187250181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143794513200269583000241 857845884900202187250181)
                  ·
                    refine ⟨160846103418787910109409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857845884900202187250181 160846103418787910109409)
                    ·
                      rfl

theorem cell22_469870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_469870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469870 prefixEnd_469870 := by exact prefixLift 469870
  have htrace : WordTrace (prefixWord ++ tailWord_469870) baseStart_469870 baseEnd_469870 := by
    simpa [prefixWord, tailWord_469870, baseEnd_469870] using wordTrace_append hprefix tailTrace_469870
  have hstable : (prefixWord ++ tailWord_469870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469870).length < 2 ^ (prefixWord ++ tailWord_469870).sum := by decide
  have hdescent : baseEnd_469870 < baseStart_469870 := by decide
  rcases family_descends (prefixWord ++ tailWord_469870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469883 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 1, 3]
def baseStart_469883 : Nat := 118140960795 + 469883 * 2 ^ 59
def prefixEnd_469883 : Nat := 4983230072969 + 3 ^ 40 * 469883 * 2
def baseEnd_469883 : Nat := 160850553584460209534369

theorem tailTrace_469883 : CollatzResearch.WordTrace tailWord_469883 prefixEnd_469883 160850553584460209534369 := by
  unfold tailWord_469883
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138040956701615472510303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11425360637801076981673535 17138040956701615472510303)
  ·
    refine ⟨25707061435052423208765455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138040956701615472510303 25707061435052423208765455)
    ·
      refine ⟨38560592152578634813148183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25707061435052423208765455 38560592152578634813148183)
      ·
        refine ⟨57840888228867952219722275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38560592152578634813148183 57840888228867952219722275)
        ·
          refine ⟨86761332343301928329583413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57840888228867952219722275 86761332343301928329583413)
          ·
            refine ⟨8133874907184555780898445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86761332343301928329583413 8133874907184555780898445)
            ·
              refine ⟨3050203090194208417836917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8133874907184555780898445 3050203090194208417836917)
              ·
                refine ⟨285956539705707039172211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3050203090194208417836917 285956539705707039172211)
                ·
                  refine ⟨428934809558560558758317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285956539705707039172211 428934809558560558758317)
                  ·
                    refine ⟨160850553584460209534369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428934809558560558758317 160850553584460209534369)
                    ·
                      rfl

theorem cell22_469883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 3].length) (baseStart_469883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469883 prefixEnd_469883 := by exact prefixLift 469883
  have htrace : WordTrace (prefixWord ++ tailWord_469883) baseStart_469883 baseEnd_469883 := by
    simpa [prefixWord, tailWord_469883, baseEnd_469883] using wordTrace_append hprefix tailTrace_469883
  have hstable : (prefixWord ++ tailWord_469883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469883).length < 2 ^ (prefixWord ++ tailWord_469883).sum := by decide
  have hdescent : baseEnd_469883 < baseStart_469883 := by decide
  rcases family_descends (prefixWord ++ tailWord_469883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469896 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_469896 : Nat := 118140960795 + 469896 * 2 ^ 59
def prefixEnd_469896 : Nat := 4983230072969 + 3 ^ 40 * 469896 * 2
def baseEnd_469896 : Nat := 53618334583377502986443

theorem tailTrace_469896 : CollatzResearch.WordTrace tailWord_469896 prefixEnd_469896 53618334583377502986443 := by
  unfold tailWord_469896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569257552827259346366771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11425676737103012461822361 8569257552827259346366771)
  ·
    refine ⟨12853886329240889019550157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8569257552827259346366771 12853886329240889019550157)
    ·
      refine ⟨4820207373465333382331309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12853886329240889019550157 4820207373465333382331309)
      ·
        refine ⟨1807577765049500018374241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4820207373465333382331309 1807577765049500018374241)
        ·
          refine ⟨1355683323787125013780681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807577765049500018374241 1355683323787125013780681)
          ·
            refine ⟨1016762492840343760335511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355683323787125013780681 1016762492840343760335511)
            ·
              refine ⟨1525143739260515640503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016762492840343760335511 1525143739260515640503267)
              ·
                refine ⟨2287715608890773460754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525143739260515640503267 2287715608890773460754901)
                ·
                  refine ⟨53618334583377502986443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2287715608890773460754901 53618334583377502986443)
                  ·
                    rfl

theorem cell22_469896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_469896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_469896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_469896 prefixEnd_469896 := by exact prefixLift 469896
  have htrace : WordTrace (prefixWord ++ tailWord_469896) baseStart_469896 baseEnd_469896 := by
    simpa [prefixWord, tailWord_469896, baseEnd_469896] using wordTrace_append hprefix tailTrace_469896
  have hstable : (prefixWord ++ tailWord_469896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469896).length < 2 ^ (prefixWord ++ tailWord_469896).sum := by decide
  have hdescent : baseEnd_469896 < baseStart_469896 := by decide
  rcases family_descends (prefixWord ++ tailWord_469896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470052 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_470052 : Nat := 118140960795 + 470052 * 2 ^ 59
def prefixEnd_470052 : Nat := 4983230072969 + 3 ^ 40 * 470052 * 2
def baseEnd_470052 : Nat := 160908405738200102058851

theorem tailTrace_470052 : CollatzResearch.WordTrace tailWord_470052 prefixEnd_470052 160908405738200102058851 := by
  unfold tailWord_470052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572102446544678667706205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11429469928726238223608273 8572102446544678667706205)
  ·
    refine ⟨3214538417454254500389827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8572102446544678667706205 3214538417454254500389827)
    ·
      refine ⟨4821807626181381750584741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214538417454254500389827 4821807626181381750584741)
      ·
        refine ⟨904088929909009078234639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4821807626181381750584741 904088929909009078234639)
        ·
          refine ⟨1356133394863513617351959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904088929909009078234639 1356133394863513617351959)
          ·
            refine ⟨2034200092295270426027939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356133394863513617351959 2034200092295270426027939)
            ·
              refine ⟨3051300138442905639041909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034200092295270426027939 3051300138442905639041909)
              ·
                refine ⟨286059387979022403660179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3051300138442905639041909 286059387979022403660179)
                ·
                  refine ⟨429089081968533605490269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286059387979022403660179 429089081968533605490269)
                  ·
                    refine ⟨160908405738200102058851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429089081968533605490269 160908405738200102058851)
                    ·
                      rfl

theorem cell22_470052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_470052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470052 prefixEnd_470052 := by exact prefixLift 470052
  have htrace : WordTrace (prefixWord ++ tailWord_470052) baseStart_470052 baseEnd_470052 := by
    simpa [prefixWord, tailWord_470052, baseEnd_470052] using wordTrace_append hprefix tailTrace_470052
  have hstable : (prefixWord ++ tailWord_470052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470052).length < 2 ^ (prefixWord ++ tailWord_470052).sum := by decide
  have hdescent : baseEnd_470052 < baseStart_470052 := by decide
  rcases family_descends (prefixWord ++ tailWord_470052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470108 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_470108 : Nat := 118140960795 + 470108 * 2 ^ 59
def prefixEnd_470108 : Nat := 4983230072969 + 3 ^ 40 * 470108 * 2
def baseEnd_470108 : Nat := 160927575682634622658679

theorem tailTrace_470108 : CollatzResearch.WordTrace tailWord_470108 prefixEnd_470108 160927575682634622658679 := by
  unfold tailWord_470108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573123690443239449725489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11430831587257652599633985 8573123690443239449725489)
  ·
    refine ⟨6429842767832429587294117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8573123690443239449725489 6429842767832429587294117)
    ·
      refine ⟨1205595518968580547617647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6429842767832429587294117 1205595518968580547617647)
      ·
        refine ⟨1808393278452870821426471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205595518968580547617647 1808393278452870821426471)
        ·
          refine ⟨2712589917679306232139707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808393278452870821426471 2712589917679306232139707)
          ·
            refine ⟨4068884876518959348209561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712589917679306232139707 4068884876518959348209561)
            ·
              refine ⟨3051663657389219511157171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068884876518959348209561 3051663657389219511157171)
              ·
                refine ⟨4577495486083829266735757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051663657389219511157171 4577495486083829266735757)
                ·
                  refine ⟨1716560807281435975025909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4577495486083829266735757 1716560807281435975025909)
                  ·
                    refine ⟨160927575682634622658679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1716560807281435975025909 160927575682634622658679)
                    ·
                      rfl

theorem cell22_470108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_470108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470108 prefixEnd_470108 := by exact prefixLift 470108
  have htrace : WordTrace (prefixWord ++ tailWord_470108) baseStart_470108 baseEnd_470108 := by
    simpa [prefixWord, tailWord_470108, baseEnd_470108] using wordTrace_append hprefix tailTrace_470108
  have hstable : (prefixWord ++ tailWord_470108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470108).length < 2 ^ (prefixWord ++ tailWord_470108).sum := by decide
  have hdescent : baseEnd_470108 < baseStart_470108 := by decide
  rcases family_descends (prefixWord ++ tailWord_470108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470121 : List Nat := [1, 2, 1, 1, 1, 6, 10]
def baseStart_470121 : Nat := 118140960795 + 470121 * 2 ^ 59
def prefixEnd_470121 : Nat := 4983230072969 + 3 ^ 40 * 470121 * 2
def baseEnd_470121 : Nat := 5960445401789145262357

theorem tailTrace_470121 : CollatzResearch.WordTrace tailWord_470121 prefixEnd_470121 5960445401789145262357 := by
  unfold tailWord_470121
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146721529839382119674217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11431147686559588079782811 17146721529839382119674217)
  ·
    refine ⟨12860041147379536589755663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17146721529839382119674217 12860041147379536589755663)
    ·
      refine ⟨19290061721069304884633495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860041147379536589755663 19290061721069304884633495)
      ·
        refine ⟨28935092581603957326950243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19290061721069304884633495 28935092581603957326950243)
        ·
          refine ⟨43402638872405935990425365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935092581603957326950243 43402638872405935990425365)
          ·
            refine ⟨2034498697144028249551189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43402638872405935990425365 2034498697144028249551189)
            ·
              refine ⟨5960445401789145262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2034498697144028249551189 5960445401789145262357)
              ·
                rfl

theorem cell22_470121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 10].length) (baseStart_470121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470121 prefixEnd_470121 := by exact prefixLift 470121
  have htrace : WordTrace (prefixWord ++ tailWord_470121) baseStart_470121 baseEnd_470121 := by
    simpa [prefixWord, tailWord_470121, baseEnd_470121] using wordTrace_append hprefix tailTrace_470121
  have hstable : (prefixWord ++ tailWord_470121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470121).length < 2 ^ (prefixWord ++ tailWord_470121).sum := by decide
  have hdescent : baseEnd_470121 < baseStart_470121 := by decide
  rcases family_descends (prefixWord ++ tailWord_470121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470125 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_470125 : Nat := 118140960795 + 470125 * 2 ^ 59
def prefixEnd_470125 : Nat := 4983230072969 + 3 ^ 40 * 470125 * 2
def baseEnd_470125 : Nat := 160933395130052244983627

theorem tailTrace_470125 : CollatzResearch.WordTrace tailWord_470125 prefixEnd_470125 160933395130052244983627 := by
  unfold tailWord_470125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146867421824890802819829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11431244947883260535213219 17146867421824890802819829)
  ·
    refine ⟨1607518820796083512764359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17146867421824890802819829 1607518820796083512764359)
    ·
      refine ⟨2411278231194125269146539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607518820796083512764359 2411278231194125269146539)
      ·
        refine ⟨3616917346791187903719809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411278231194125269146539 3616917346791187903719809)
        ·
          refine ⟨2712688010093390927789857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3616917346791187903719809 2712688010093390927789857)
          ·
            refine ⟨2034516007570043195842393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712688010093390927789857 2034516007570043195842393)
            ·
              refine ⟨1525887005677532396881795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034516007570043195842393 1525887005677532396881795)
              ·
                refine ⟨2288830508516298595322693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525887005677532396881795 2288830508516298595322693)
                ·
                  refine ⟨429155720346805986623005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288830508516298595322693 429155720346805986623005)
                  ·
                    refine ⟨160933395130052244983627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429155720346805986623005 160933395130052244983627)
                    ·
                      rfl

theorem cell22_470125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_470125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470125 prefixEnd_470125 := by exact prefixLift 470125
  have htrace : WordTrace (prefixWord ++ tailWord_470125) baseStart_470125 baseEnd_470125 := by
    simpa [prefixWord, tailWord_470125, baseEnd_470125] using wordTrace_append hprefix tailTrace_470125
  have hstable : (prefixWord ++ tailWord_470125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470125).length < 2 ^ (prefixWord ++ tailWord_470125).sum := by decide
  have hdescent : baseEnd_470125 < baseStart_470125 := by decide
  rcases family_descends (prefixWord ++ tailWord_470125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470326 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_470326 : Nat := 118140960795 + 470326 * 2 ^ 59
def prefixEnd_470326 : Nat := 4983230072969 + 3 ^ 40 * 470326 * 2
def baseEnd_470326 : Nat := 161002201537754720708011

theorem tailTrace_470326 : CollatzResearch.WordTrace tailWord_470326 prefixEnd_470326 161002201537754720708011 := by
  unfold tailWord_470326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072137405881043883180427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11436132329397801420591221 1072137405881043883180427)
  ·
    refine ⟨1608206108821565824770641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1072137405881043883180427 1608206108821565824770641)
    ·
      refine ⟨1206154581616174368577981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1608206108821565824770641 1206154581616174368577981)
      ·
        refine ⟨452307968106065388216743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1206154581616174368577981 452307968106065388216743)
        ·
          refine ⟨678461952159098082325115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452307968106065388216743 678461952159098082325115)
          ·
            refine ⟨1017692928238647123487673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678461952159098082325115 1017692928238647123487673)
            ·
              refine ⟨763269696178985342615755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017692928238647123487673 763269696178985342615755)
              ·
                refine ⟨1144904544268478013923633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763269696178985342615755 1144904544268478013923633)
                ·
                  refine ⟨858678408201358510442725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144904544268478013923633 858678408201358510442725)
                  ·
                    refine ⟨161002201537754720708011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 858678408201358510442725 161002201537754720708011)
                    ·
                      rfl

theorem cell22_470326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_470326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470326 prefixEnd_470326 := by exact prefixLift 470326
  have htrace : WordTrace (prefixWord ++ tailWord_470326) baseStart_470326 baseEnd_470326 := by
    simpa [prefixWord, tailWord_470326, baseEnd_470326] using wordTrace_append hprefix tailTrace_470326
  have hstable : (prefixWord ++ tailWord_470326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470326).length < 2 ^ (prefixWord ++ tailWord_470326).sum := by decide
  have hdescent : baseEnd_470326 < baseStart_470326 := by decide
  rcases family_descends (prefixWord ++ tailWord_470326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470350 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_470350 : Nat := 118140960795 + 470350 * 2 ^ 59
def prefixEnd_470350 : Nat := 4983230072969 + 3 ^ 40 * 470350 * 2
def baseEnd_470350 : Nat := 161010417228226658107937

theorem tailTrace_470350 : CollatzResearch.WordTrace tailWord_470350 prefixEnd_470350 161010417228226658107937 := by
  unfold tailWord_470350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144384230751219278720063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11436715897339836153173669 2144384230751219278720063)
  ·
    refine ⟨3216576346126828918080095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144384230751219278720063 3216576346126828918080095)
    ·
      refine ⟨4824864519190243377120143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3216576346126828918080095 4824864519190243377120143)
      ·
        refine ⟨7237296778785365065680215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4824864519190243377120143 7237296778785365065680215)
        ·
          refine ⟨10855945168178047598520323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237296778785365065680215 10855945168178047598520323)
          ·
            refine ⟨16283917752267071397780485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855945168178047598520323 16283917752267071397780485)
            ·
              refine ⟨3053234578550075887083841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16283917752267071397780485 3053234578550075887083841)
              ·
                refine ⟨2289925933912556915312881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053234578550075887083841 2289925933912556915312881)
                ·
                  refine ⟨1717444450434417686484661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2289925933912556915312881 1717444450434417686484661)
                  ·
                    refine ⟨161010417228226658107937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1717444450434417686484661 161010417228226658107937)
                    ·
                      rfl

theorem cell22_470350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_470350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470350 prefixEnd_470350 := by exact prefixLift 470350
  have htrace : WordTrace (prefixWord ++ tailWord_470350) baseStart_470350 baseEnd_470350 := by
    simpa [prefixWord, tailWord_470350, baseEnd_470350] using wordTrace_append hprefix tailTrace_470350
  have hstable : (prefixWord ++ tailWord_470350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470350).length < 2 ^ (prefixWord ++ tailWord_470350).sum := by decide
  have hdescent : baseEnd_470350 < baseStart_470350 := by decide
  rcases family_descends (prefixWord ++ tailWord_470350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470358 : List Nat := [5, 2, 3, 1, 1, 2, 1, 7]
def baseStart_470358 : Nat := 118140960795 + 470358 * 2 ^ 59
def prefixEnd_470358 : Nat := 4983230072969 + 3 ^ 40 * 470358 * 2
def baseEnd_470358 : Nat := 17890350643524144878657

theorem tailTrace_470358 : CollatzResearch.WordTrace tailWord_470358 prefixEnd_470358 17890350643524144878657 := by
  unfold tailWord_470358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072210351873798224753233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11436910419987181064034485 1072210351873798224753233)
  ·
    refine ⟨804157763905348668564925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1072210351873798224753233 804157763905348668564925)
    ·
      refine ⟨301559161464505750711847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 804157763905348668564925 301559161464505750711847)
      ·
        refine ⟨452338742196758626067771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301559161464505750711847 452338742196758626067771)
        ·
          refine ⟨678508113295137939101657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452338742196758626067771 678508113295137939101657)
          ·
            refine ⟨508881084971353454326243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678508113295137939101657 508881084971353454326243)
            ·
              refine ⟨763321627457030181489365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508881084971353454326243 763321627457030181489365)
              ·
                refine ⟨17890350643524144878657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 763321627457030181489365 17890350643524144878657)
                ·
                  rfl

theorem cell22_470358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_470358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470358 prefixEnd_470358 := by exact prefixLift 470358
  have htrace : WordTrace (prefixWord ++ tailWord_470358) baseStart_470358 baseEnd_470358 := by
    simpa [prefixWord, tailWord_470358, baseEnd_470358] using wordTrace_append hprefix tailTrace_470358
  have hstable : (prefixWord ++ tailWord_470358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470358).length < 2 ^ (prefixWord ++ tailWord_470358).sum := by decide
  have hdescent : baseEnd_470358 < baseStart_470358 := by decide
  rcases family_descends (prefixWord ++ tailWord_470358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470380 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_470380 : Nat := 118140960795 + 470380 * 2 ^ 59
def prefixEnd_470380 : Nat := 4983230072969 + 3 ^ 40 * 470380 * 2
def baseEnd_470380 : Nat := 53673562280438859952615

theorem tailTrace_470380 : CollatzResearch.WordTrace tailWord_470380 prefixEnd_470380 53673562280438859952615 := by
  unfold tailWord_470380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578084017950534676676297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11437445357267379568901729 8578084017950534676676297)
  ·
    refine ⟨6433563013462901007507223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8578084017950534676676297 6433563013462901007507223)
    ·
      refine ⟨9650344520194351511260835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433563013462901007507223 9650344520194351511260835)
      ·
        refine ⟨14475516780291527266891253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650344520194351511260835 14475516780291527266891253)
        ·
          refine ⟨1357079698152330681271055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14475516780291527266891253 1357079698152330681271055)
          ·
            refine ⟨2035619547228496021906583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357079698152330681271055 2035619547228496021906583)
            ·
              refine ⟨3053429320842744032859875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035619547228496021906583 3053429320842744032859875)
              ·
                refine ⟨4580143981264116049289813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053429320842744032859875 4580143981264116049289813)
                ·
                  refine ⟨53673562280438859952615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4580143981264116049289813 53673562280438859952615)
                  ·
                    rfl

theorem cell22_470380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_470380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470380 prefixEnd_470380 := by exact prefixLift 470380
  have htrace : WordTrace (prefixWord ++ tailWord_470380) baseStart_470380 baseEnd_470380 := by
    simpa [prefixWord, tailWord_470380, baseEnd_470380] using wordTrace_append hprefix tailTrace_470380
  have hstable : (prefixWord ++ tailWord_470380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470380).length < 2 ^ (prefixWord ++ tailWord_470380).sum := by decide
  have hdescent : baseEnd_470380 < baseStart_470380 := by decide
  rcases family_descends (prefixWord ++ tailWord_470380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470395 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_470395 : Nat := 118140960795 + 470395 * 2 ^ 59
def prefixEnd_470395 : Nat := 4983230072969 + 3 ^ 40 * 470395 * 2
def baseEnd_470395 : Nat := 161025821647861540732799

theorem tailTrace_470395 : CollatzResearch.WordTrace tailWord_470395 prefixEnd_470395 161025821647861540732799 := by
  unfold tailWord_470395
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156715130846726915148639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11437810087231151276765759 17156715130846726915148639)
  ·
    refine ⟨25735072696270090372722959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17156715130846726915148639 25735072696270090372722959)
    ·
      refine ⟨38602609044405135559084439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25735072696270090372722959 38602609044405135559084439)
      ·
        refine ⟨57903913566607703338626659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38602609044405135559084439 57903913566607703338626659)
        ·
          refine ⟨86855870349911555007939989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57903913566607703338626659 86855870349911555007939989)
          ·
            refine ⟨4071368922652104140997187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86855870349911555007939989 4071368922652104140997187)
            ·
              refine ⟨6107053383978156211495781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071368922652104140997187 6107053383978156211495781)
              ·
                refine ⟨1145072509495904289655459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6107053383978156211495781 1145072509495904289655459)
                ·
                  refine ⟨1717608764243856434483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145072509495904289655459 1717608764243856434483189)
                  ·
                    refine ⟨161025821647861540732799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1717608764243856434483189 161025821647861540732799)
                    ·
                      rfl

theorem cell22_470395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_470395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470395 prefixEnd_470395 := by exact prefixLift 470395
  have htrace : WordTrace (prefixWord ++ tailWord_470395) baseStart_470395 baseEnd_470395 := by
    simpa [prefixWord, tailWord_470395, baseEnd_470395] using wordTrace_append hprefix tailTrace_470395
  have hstable : (prefixWord ++ tailWord_470395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470395).length < 2 ^ (prefixWord ++ tailWord_470395).sum := by decide
  have hdescent : baseEnd_470395 < baseStart_470395 := by decide
  rcases family_descends (prefixWord ++ tailWord_470395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470412 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_470412 : Nat := 118140960795 + 470412 * 2 ^ 59
def prefixEnd_470412 : Nat := 4983230072969 + 3 ^ 40 * 470412 * 2
def baseEnd_470412 : Nat := 161031641095279163057747

theorem tailTrace_470412 : CollatzResearch.WordTrace tailWord_470412 prefixEnd_470412 161031641095279163057747 := by
  unfold tailWord_470412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578667585892569409258745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11438223447856759212344993 8578667585892569409258745)
  ·
    refine ⟨6434000689419427056944059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8578667585892569409258745 6434000689419427056944059)
    ·
      refine ⟨9651001034129140585416089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434000689419427056944059 9651001034129140585416089)
      ·
        refine ⟨7238250775596855439062067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9651001034129140585416089 7238250775596855439062067)
        ·
          refine ⟨10857376163395283158593101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7238250775596855439062067 10857376163395283158593101)
          ·
            refine ⟨4071516061273231184472413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10857376163395283158593101 4071516061273231184472413)
            ·
              refine ⟨1526818522977461694177155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4071516061273231184472413 1526818522977461694177155)
              ·
                refine ⟨2290227784466192541265733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526818522977461694177155 2290227784466192541265733)
                ·
                  refine ⟨429417709587411101487325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290227784466192541265733 429417709587411101487325)
                  ·
                    refine ⟨161031641095279163057747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429417709587411101487325 161031641095279163057747)
                    ·
                      rfl

theorem cell22_470412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_470412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470412 prefixEnd_470412 := by exact prefixLift 470412
  have htrace : WordTrace (prefixWord ++ tailWord_470412) baseStart_470412 baseEnd_470412 := by
    simpa [prefixWord, tailWord_470412, baseEnd_470412] using wordTrace_append hprefix tailTrace_470412
  have hstable : (prefixWord ++ tailWord_470412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470412).length < 2 ^ (prefixWord ++ tailWord_470412).sum := by decide
  have hdescent : baseEnd_470412 < baseStart_470412 := by decide
  rcases family_descends (prefixWord ++ tailWord_470412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470414 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_470414 : Nat := 118140960795 + 470414 * 2 ^ 59
def prefixEnd_470414 : Nat := 4983230072969 + 3 ^ 40 * 470414 * 2
def baseEnd_470414 : Nat := 53677441912050608169247

theorem tailTrace_470414 : CollatzResearch.WordTrace tailWord_470414 prefixEnd_470414 53677441912050608169247 := by
  unfold tailWord_470414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144676014722236645011287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11438272078518595440060197 2144676014722236645011287)
  ·
    refine ⟨3217014022083354967516931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144676014722236645011287 3217014022083354967516931)
    ·
      refine ⟨4825521033125032451275397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217014022083354967516931 4825521033125032451275397)
      ·
        refine ⟨904785193710943584614137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4825521033125032451275397 904785193710943584614137)
        ·
          refine ⟨678588895283207688460603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904785193710943584614137 678588895283207688460603)
          ·
            refine ⟨1017883342924811532690905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678588895283207688460603 1017883342924811532690905)
            ·
              refine ⟨763412507193608649518179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017883342924811532690905 763412507193608649518179)
              ·
                refine ⟨1145118760790412974277269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763412507193608649518179 1145118760790412974277269)
                ·
                  refine ⟨53677441912050608169247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1145118760790412974277269 53677441912050608169247)
                  ·
                    rfl

theorem cell22_470414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_470414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470414 prefixEnd_470414 := by exact prefixLift 470414
  have htrace : WordTrace (prefixWord ++ tailWord_470414) baseStart_470414 baseEnd_470414 := by
    simpa [prefixWord, tailWord_470414, baseEnd_470414] using wordTrace_append hprefix tailTrace_470414
  have hstable : (prefixWord ++ tailWord_470414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470414).length < 2 ^ (prefixWord ++ tailWord_470414).sum := by decide
  have hdescent : baseEnd_470414 < baseStart_470414 := by decide
  rcases family_descends (prefixWord ++ tailWord_470414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470429 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_470429 : Nat := 118140960795 + 470429 * 2 ^ 59
def prefixEnd_470429 : Nat := 4983230072969 + 3 ^ 40 * 470429 * 2
def baseEnd_470429 : Nat := 161037460542696785382695

theorem tailTrace_470429 : CollatzResearch.WordTrace tailWord_470429 prefixEnd_470429 161037460542696785382695 := by
  unfold tailWord_470429
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157955212723550721886341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11438636808482367147924227 17157955212723550721886341)
  ·
    refine ⟨3217116602385665760353689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17157955212723550721886341 3217116602385665760353689)
    ·
      refine ⟨2412837451789249320265267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3217116602385665760353689 2412837451789249320265267)
      ·
        refine ⟨3619256177683873980397901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412837451789249320265267 3619256177683873980397901)
        ·
          refine ⟨1357221066631452742649213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3619256177683873980397901 1357221066631452742649213)
          ·
            refine ⟨508957899986794778493455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357221066631452742649213 508957899986794778493455)
            ·
              refine ⟨763436849980192167740183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508957899986794778493455 763436849980192167740183)
              ·
                refine ⟨1145155274970288251610275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763436849980192167740183 1145155274970288251610275)
                ·
                  refine ⟨1717732912455432377415413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145155274970288251610275 1717732912455432377415413)
                  ·
                    refine ⟨161037460542696785382695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1717732912455432377415413 161037460542696785382695)
                    ·
                      rfl

theorem cell22_470429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_470429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470429 prefixEnd_470429 := by exact prefixLift 470429
  have htrace : WordTrace (prefixWord ++ tailWord_470429) baseStart_470429 baseEnd_470429 := by
    simpa [prefixWord, tailWord_470429, baseEnd_470429] using wordTrace_append hprefix tailTrace_470429
  have hstable : (prefixWord ++ tailWord_470429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470429).length < 2 ^ (prefixWord ++ tailWord_470429).sum := by decide
  have hdescent : baseEnd_470429 < baseStart_470429 := by decide
  rcases family_descends (prefixWord ++ tailWord_470429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470474 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_470474 : Nat := 118140960795 + 470474 * 2 ^ 59
def prefixEnd_470474 : Nat := 4983230072969 + 3 ^ 40 * 470474 * 2
def baseEnd_470474 : Nat := 161052864962331668007557

theorem tailTrace_470474 : CollatzResearch.WordTrace tailWord_470474 prefixEnd_470474 161052864962331668007557 := by
  unfold tailWord_470474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289899124390130851818619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11439730998373682271516317 4289899124390130851818619)
  ·
    refine ⟨6434848686585196277727929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289899124390130851818619 6434848686585196277727929)
    ·
      refine ⟨4826136514938897208295947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6434848686585196277727929 4826136514938897208295947)
      ·
        refine ⟨7239204772408345812443921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826136514938897208295947 7239204772408345812443921)
        ·
          refine ⟨5429403579306259359332941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7239204772408345812443921 5429403579306259359332941)
          ·
            refine ⟨2036026342239847259749853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5429403579306259359332941 2036026342239847259749853)
            ·
              refine ⟨763509878339942722406195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036026342239847259749853 763509878339942722406195)
              ·
                refine ⟨1145264817509914083609293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763509878339942722406195 1145264817509914083609293)
                ·
                  refine ⟨429474306566217781353485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145264817509914083609293 429474306566217781353485)
                  ·
                    refine ⟨161052864962331668007557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429474306566217781353485 161052864962331668007557)
                    ·
                      rfl

theorem cell22_470474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_470474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470474 prefixEnd_470474 := by exact prefixLift 470474
  have htrace : WordTrace (prefixWord ++ tailWord_470474) baseStart_470474 baseEnd_470474 := by
    simpa [prefixWord, tailWord_470474, baseEnd_470474] using wordTrace_append hprefix tailTrace_470474
  have hstable : (prefixWord ++ tailWord_470474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470474).length < 2 ^ (prefixWord ++ tailWord_470474).sum := by decide
  have hdescent : baseEnd_470474 < baseStart_470474 := by decide
  rcases family_descends (prefixWord ++ tailWord_470474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470515 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 10]
def baseStart_470515 : Nat := 118140960795 + 470515 * 2 ^ 59
def prefixEnd_470515 : Nat := 4983230072969 + 3 ^ 40 * 470515 * 2
def baseEnd_470515 : Nat := 53688966700073742577477

theorem tailTrace_470515 : CollatzResearch.WordTrace tailWord_470515 prefixEnd_470515 53688966700073742577477 := by
  unfold tailWord_470515
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161091890411987409516999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11440727926941324939677999 17161091890411987409516999)
  ·
    refine ⟨25741637835617981114275499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17161091890411987409516999 25741637835617981114275499)
    ·
      refine ⟨38612456753426971671413249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25741637835617981114275499 38612456753426971671413249)
      ·
        refine ⟨28959342565070228753559937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38612456753426971671413249 28959342565070228753559937)
        ·
          refine ⟨21719506923802671565169953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28959342565070228753559937 21719506923802671565169953)
          ·
            refine ⟨16289630192852003673877465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21719506923802671565169953 16289630192852003673877465)
            ·
              refine ⟨12217222644639002755408099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16289630192852003673877465 12217222644639002755408099)
              ·
                refine ⟨18325833966958504133112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217222644639002755408099 18325833966958504133112149)
                ·
                  refine ⟨53688966700073742577477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18325833966958504133112149 53688966700073742577477)
                  ·
                    rfl

theorem cell22_470515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_470515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470515 prefixEnd_470515 := by exact prefixLift 470515
  have htrace : WordTrace (prefixWord ++ tailWord_470515) baseStart_470515 baseEnd_470515 := by
    simpa [prefixWord, tailWord_470515, baseEnd_470515] using wordTrace_append hprefix tailTrace_470515
  have hstable : (prefixWord ++ tailWord_470515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470515).length < 2 ^ (prefixWord ++ tailWord_470515).sum := by decide
  have hdescent : baseEnd_470515 < baseStart_470515 := by decide
  rcases family_descends (prefixWord ++ tailWord_470515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470547 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_470547 : Nat := 118140960795 + 470547 * 2 ^ 59
def prefixEnd_470547 : Nat := 4983230072969 + 3 ^ 40 * 470547 * 2
def baseEnd_470547 : Nat := 161077854354183810932333

theorem tailTrace_470547 : CollatzResearch.WordTrace tailWord_470547 prefixEnd_470547 161077854354183810932333 := by
  unfold tailWord_470547
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162259026296056874681895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11441506017530704583121263 17162259026296056874681895)
  ·
    refine ⟨25743388539444085312022843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17162259026296056874681895 25743388539444085312022843)
    ·
      refine ⟨38615082809166127968034265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25743388539444085312022843 38615082809166127968034265)
      ·
        refine ⟨28961312106874595976025699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38615082809166127968034265 28961312106874595976025699)
        ·
          refine ⟨43441968160311893964038549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28961312106874595976025699 43441968160311893964038549)
          ·
            refine ⟨2036342257514620029564307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43441968160311893964038549 2036342257514620029564307)
            ·
              refine ⟨3054513386271930044346461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036342257514620029564307 3054513386271930044346461)
              ·
                refine ⟨1145442519851973766629923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3054513386271930044346461 1145442519851973766629923)
                ·
                  refine ⟨1718163779777960649944885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145442519851973766629923 1718163779777960649944885)
                  ·
                    refine ⟨161077854354183810932333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718163779777960649944885 161077854354183810932333)
                    ·
                      rfl

theorem cell22_470547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_470547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470547 prefixEnd_470547 := by exact prefixLift 470547
  have htrace : WordTrace (prefixWord ++ tailWord_470547) baseStart_470547 baseEnd_470547 := by
    simpa [prefixWord, tailWord_470547, baseEnd_470547] using wordTrace_append hprefix tailTrace_470547
  have hstable : (prefixWord ++ tailWord_470547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470547).length < 2 ^ (prefixWord ++ tailWord_470547).sum := by decide
  have hdescent : baseEnd_470547 < baseStart_470547 := by decide
  rcases family_descends (prefixWord ++ tailWord_470547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470581 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_470581 : Nat := 118140960795 + 470581 * 2 ^ 59
def prefixEnd_470581 : Nat := 4983230072969 + 3 ^ 40 * 470581 * 2
def baseEnd_470581 : Nat := 161089493249019055582229

theorem tailTrace_470581 : CollatzResearch.WordTrace tailWord_470581 prefixEnd_470581 161089493249019055582229 := by
  unfold tailWord_470581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163499108172880681419597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11442332738781920454279731 17163499108172880681419597)
  ·
    refine ⟨6436312165564830255532349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17163499108172880681419597 6436312165564830255532349)
    ·
      refine ⟨2413617062086811345824631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6436312165564830255532349 2413617062086811345824631)
      ·
        refine ⟨3620425593130217018736947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413617062086811345824631 3620425593130217018736947)
        ·
          refine ⟨5430638389695325528105421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620425593130217018736947 5430638389695325528105421)
          ·
            refine ⟨2036489396135747073039533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5430638389695325528105421 2036489396135747073039533)
            ·
              refine ⟨763683523550905152389825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036489396135747073039533 763683523550905152389825)
              ·
                refine ⟨572762642663178864292369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763683523550905152389825 572762642663178864292369)
                ·
                  refine ⟨429571981997384148219277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572762642663178864292369 429571981997384148219277)
                  ·
                    refine ⟨161089493249019055582229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429571981997384148219277 161089493249019055582229)
                    ·
                      rfl

theorem cell22_470581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_470581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470581 prefixEnd_470581 := by exact prefixLift 470581
  have htrace : WordTrace (prefixWord ++ tailWord_470581) baseStart_470581 baseEnd_470581 := by
    simpa [prefixWord, tailWord_470581, baseEnd_470581] using wordTrace_append hprefix tailTrace_470581
  have hstable : (prefixWord ++ tailWord_470581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470581).length < 2 ^ (prefixWord ++ tailWord_470581).sum := by decide
  have hdescent : baseEnd_470581 < baseStart_470581 := by decide
  rcases family_descends (prefixWord ++ tailWord_470581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470609 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_470609 : Nat := 118140960795 + 470609 * 2 ^ 59
def prefixEnd_470609 : Nat := 4983230072969 + 3 ^ 40 * 470609 * 2
def baseEnd_470609 : Nat := 161099078221236315882143

theorem tailTrace_470609 : CollatzResearch.WordTrace tailWord_470609 prefixEnd_470609 161099078221236315882143 := by
  unfold tailWord_470609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164520352071441463438881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11443013568047627642292587 17164520352071441463438881)
  ·
    refine ⟨12873390264053581097579161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164520352071441463438881 12873390264053581097579161)
    ·
      refine ⟨9655042698040185823184371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12873390264053581097579161 9655042698040185823184371)
      ·
        refine ⟨14482564047060278734776557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655042698040185823184371 14482564047060278734776557)
        ·
          refine ⟨5430961517647604525541209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14482564047060278734776557 5430961517647604525541209)
          ·
            refine ⟨4073221138235703394155907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430961517647604525541209 4073221138235703394155907)
            ·
              refine ⟨6109831707353555091233861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073221138235703394155907 6109831707353555091233861)
              ·
                refine ⟨1145593445128791579606349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6109831707353555091233861 1145593445128791579606349)
                ·
                  refine ⟨429597541923296842352381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145593445128791579606349 429597541923296842352381)
                  ·
                    refine ⟨161099078221236315882143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429597541923296842352381 161099078221236315882143)
                    ·
                      rfl

theorem cell22_470609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_470609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470609 prefixEnd_470609 := by exact prefixLift 470609
  have htrace : WordTrace (prefixWord ++ tailWord_470609) baseStart_470609 baseEnd_470609 := by
    simpa [prefixWord, tailWord_470609, baseEnd_470609] using wordTrace_append hprefix tailTrace_470609
  have hstable : (prefixWord ++ tailWord_470609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470609).length < 2 ^ (prefixWord ++ tailWord_470609).sum := by decide
  have hdescent : baseEnd_470609 < baseStart_470609 := by decide
  rcases family_descends (prefixWord ++ tailWord_470609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470652 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_470652 : Nat := 118140960795 + 470652 * 2 ^ 59
def prefixEnd_470652 : Nat := 4983230072969 + 3 ^ 40 * 470652 * 2
def baseEnd_470652 : Nat := 161113797999998537057011

theorem tailTrace_470652 : CollatzResearch.WordTrace tailWord_470652 prefixEnd_470652 161113797999998537057011 := by
  unfold tailWord_470652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583044345457829903627105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11444059127277106538169473 8583044345457829903627105)
  ·
    refine ⟨6437283259093372427720329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8583044345457829903627105 6437283259093372427720329)
    ·
      refine ⟨4827962444320029320790247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6437283259093372427720329 4827962444320029320790247)
      ·
        refine ⟨7241943666480043981185371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827962444320029320790247 7241943666480043981185371)
        ·
          refine ⟨10862915499720065971778057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241943666480043981185371 10862915499720065971778057)
          ·
            refine ⟨8147186624790049478833543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10862915499720065971778057 8147186624790049478833543)
            ·
              refine ⟨12220779937185074218250315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147186624790049478833543 12220779937185074218250315)
              ·
                refine ⟨18331169905777611327375473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220779937185074218250315 18331169905777611327375473)
                ·
                  refine ⟨13748377429333208495531605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18331169905777611327375473 13748377429333208495531605)
                  ·
                    refine ⟨161113797999998537057011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13748377429333208495531605 161113797999998537057011)
                    ·
                      rfl

theorem cell22_470652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_470652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470652 prefixEnd_470652 := by exact prefixLift 470652
  have htrace : WordTrace (prefixWord ++ tailWord_470652) baseStart_470652 baseEnd_470652 := by
    simpa [prefixWord, tailWord_470652, baseEnd_470652] using wordTrace_append hprefix tailTrace_470652
  have hstable : (prefixWord ++ tailWord_470652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470652).length < 2 ^ (prefixWord ++ tailWord_470652).sum := by decide
  have hdescent : baseEnd_470652 < baseStart_470652 := by decide
  rcases family_descends (prefixWord ++ tailWord_470652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470667 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 8]
def baseStart_470667 : Nat := 118140960795 + 470667 * 2 ^ 59
def prefixEnd_470667 : Nat := 4983230072969 + 3 ^ 40 * 470667 * 2
def baseEnd_470667 : Nat := 53706310935514499310655

theorem tailTrace_470667 : CollatzResearch.WordTrace tailWord_470667 prefixEnd_470667 53706310935514499310655 := by
  unfold tailWord_470667
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166635785861317369050255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11444423857240878246033503 17166635785861317369050255)
  ·
    refine ⟨25749953678791976053575383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166635785861317369050255 25749953678791976053575383)
    ·
      refine ⟨38624930518187964080363075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25749953678791976053575383 38624930518187964080363075)
      ·
        refine ⟨57937395777281946120544613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38624930518187964080363075 57937395777281946120544613)
        ·
          refine ⟨10863261708240364897602115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57937395777281946120544613 10863261708240364897602115)
          ·
            refine ⟨16294892562360547346403173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863261708240364897602115 16294892562360547346403173)
            ·
              refine ⟨3055292355442602627450595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16294892562360547346403173 3055292355442602627450595)
              ·
                refine ⟨4582938533163903941175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055292355442602627450595 4582938533163903941175893)
                ·
                  refine ⟨53706310935514499310655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4582938533163903941175893 53706310935514499310655)
                  ·
                    rfl

theorem cell22_470667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_470667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470667 prefixEnd_470667 := by exact prefixLift 470667
  have htrace : WordTrace (prefixWord ++ tailWord_470667) baseStart_470667 baseEnd_470667 := by
    simpa [prefixWord, tailWord_470667, baseEnd_470667] using wordTrace_append hprefix tailTrace_470667
  have hstable : (prefixWord ++ tailWord_470667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470667).length < 2 ^ (prefixWord ++ tailWord_470667).sum := by decide
  have hdescent : baseEnd_470667 < baseStart_470667 := by decide
  rcases family_descends (prefixWord ++ tailWord_470667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470716 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_470716 : Nat := 118140960795 + 470716 * 2 ^ 59
def prefixEnd_470716 : Nat := 4983230072969 + 3 ^ 40 * 470716 * 2
def baseEnd_470716 : Nat := 161135706507923703456815

theorem tailTrace_470716 : CollatzResearch.WordTrace tailWord_470716 prefixEnd_470716 161135706507923703456815 := by
  unfold tailWord_470716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584211481341899368792001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11445615308455865825056001 8584211481341899368792001)
  ·
    refine ⟨6438158611006424526594001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584211481341899368792001 6438158611006424526594001)
    ·
      refine ⟨4828618958254818394945501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6438158611006424526594001 4828618958254818394945501)
      ·
        refine ⟨1810732109345556898104563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4828618958254818394945501 1810732109345556898104563)
        ·
          refine ⟨2716098164018335347156845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810732109345556898104563 2716098164018335347156845)
          ·
            refine ⟨1018536811506875755183817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2716098164018335347156845 1018536811506875755183817)
            ·
              refine ⟨763902608630156816387863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018536811506875755183817 763902608630156816387863)
              ·
                refine ⟨1145853912945235224581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763902608630156816387863 1145853912945235224581795)
                ·
                  refine ⟨1718780869417852836872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145853912945235224581795 1718780869417852836872693)
                  ·
                    refine ⟨161135706507923703456815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718780869417852836872693 161135706507923703456815)
                    ·
                      rfl

theorem cell22_470716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_470716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470716 prefixEnd_470716 := by exact prefixLift 470716
  have htrace : WordTrace (prefixWord ++ tailWord_470716) baseStart_470716 baseEnd_470716 := by
    simpa [prefixWord, tailWord_470716, baseEnd_470716] using wordTrace_append hprefix tailTrace_470716
  have hstable : (prefixWord ++ tailWord_470716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470716).length < 2 ^ (prefixWord ++ tailWord_470716).sum := by decide
  have hdescent : baseEnd_470716 < baseStart_470716 := by decide
  rcases family_descends (prefixWord ++ tailWord_470716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470733 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_470733 : Nat := 118140960795 + 470733 * 2 ^ 59
def prefixEnd_470733 : Nat := 4983230072969 + 3 ^ 40 * 470733 * 2
def baseEnd_470733 : Nat := 161141525955341325781763

theorem tailTrace_470733 : CollatzResearch.WordTrace tailWord_470733 prefixEnd_470733 161141525955341325781763 := by
  unfold tailWord_470733
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169043003622210640952853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11446028669081473760635235 17169043003622210640952853)
  ·
    refine ⟨804798890794791123794665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17169043003622210640952853 804798890794791123794665)
    ·
      refine ⟨603599168096093342845999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804798890794791123794665 603599168096093342845999)
      ·
        refine ⟨905398752144140014268999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603599168096093342845999 905398752144140014268999)
        ·
          refine ⟨1358098128216210021403499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905398752144140014268999 1358098128216210021403499)
          ·
            refine ⟨2037147192324315032105249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358098128216210021403499 2037147192324315032105249)
            ·
              refine ⟨1527860394243236274078937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037147192324315032105249 1527860394243236274078937)
              ·
                refine ⟨1145895295682427205559203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527860394243236274078937 1145895295682427205559203)
                ·
                  refine ⟨1718842943523640808338805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145895295682427205559203 1718842943523640808338805)
                  ·
                    refine ⟨161141525955341325781763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1718842943523640808338805 161141525955341325781763)
                    ·
                      rfl

theorem cell22_470733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_470733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470733 prefixEnd_470733 := by exact prefixLift 470733
  have htrace : WordTrace (prefixWord ++ tailWord_470733) baseStart_470733 baseEnd_470733 := by
    simpa [prefixWord, tailWord_470733, baseEnd_470733] using wordTrace_append hprefix tailTrace_470733
  have hstable : (prefixWord ++ tailWord_470733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470733).length < 2 ^ (prefixWord ++ tailWord_470733).sum := by decide
  have hdescent : baseEnd_470733 < baseStart_470733 := by decide
  rcases family_descends (prefixWord ++ tailWord_470733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470797 : List Nat := [1, 7, 2, 1, 1, 2, 8]
def baseStart_470797 : Nat := 118140960795 + 470797 * 2 ^ 59
def prefixEnd_470797 : Nat := 4983230072969 + 3 ^ 40 * 470797 * 2
def baseEnd_470797 : Nat := 5969016091232092303021

theorem tailTrace_470797 : CollatzResearch.WordTrace tailWord_470797 prefixEnd_470797 5969016091232092303021 := by
  unfold tailWord_470797
  simp only [CollatzResearch.WordTrace]
  refine ⟨17171377275390349571282645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447584850260233047521763 17171377275390349571282645)
  ·
    refine ⟨402454154891961318076937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17171377275390349571282645 402454154891961318076937)
    ·
      refine ⟨301840616168970988557703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402454154891961318076937 301840616168970988557703)
      ·
        refine ⟨452760924253456482836555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301840616168970988557703 452760924253456482836555)
        ·
          refine ⟨679141386380184724254833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452760924253456482836555 679141386380184724254833)
          ·
            refine ⟨509356039785138543191125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679141386380184724254833 509356039785138543191125)
            ·
              refine ⟨5969016091232092303021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 509356039785138543191125 5969016091232092303021)
              ·
                rfl

theorem cell22_470797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 8].length) (baseStart_470797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470797 prefixEnd_470797 := by exact prefixLift 470797
  have htrace : WordTrace (prefixWord ++ tailWord_470797) baseStart_470797 baseEnd_470797 := by
    simpa [prefixWord, tailWord_470797, baseEnd_470797] using wordTrace_append hprefix tailTrace_470797
  have hstable : (prefixWord ++ tailWord_470797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470797).length < 2 ^ (prefixWord ++ tailWord_470797).sum := by decide
  have hdescent : baseEnd_470797 < baseStart_470797 := by decide
  rcases family_descends (prefixWord ++ tailWord_470797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470851 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_470851 : Nat := 118140960795 + 470851 * 2 ^ 59
def prefixEnd_470851 : Nat := 4983230072969 + 3 ^ 40 * 470851 * 2
def baseEnd_470851 : Nat := 161181919766828351331401

theorem tailTrace_470851 : CollatzResearch.WordTrace tailWord_470851 prefixEnd_470851 161181919766828351331401 := by
  unfold tailWord_470851
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173346817194716793748407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11448897878129811195832271 17173346817194716793748407)
  ·
    refine ⟨25760020225792075190622611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173346817194716793748407 25760020225792075190622611)
    ·
      refine ⟨38640030338688112785933917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760020225792075190622611 38640030338688112785933917)
      ·
        refine ⟨14490011377008042294725219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38640030338688112785933917 14490011377008042294725219)
        ·
          refine ⟨21735017065512063442087829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490011377008042294725219 21735017065512063442087829)
          ·
            refine ⟨1018828924945877973847867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21735017065512063442087829 1018828924945877973847867)
            ·
              refine ⟨1528243387418816960771801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018828924945877973847867 1528243387418816960771801)
              ·
                refine ⟨1146182540564112720578851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528243387418816960771801 1146182540564112720578851)
                ·
                  refine ⟨1719273810846169080868277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146182540564112720578851 1719273810846169080868277)
                  ·
                    refine ⟨161181919766828351331401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1719273810846169080868277 161181919766828351331401)
                    ·
                      rfl

theorem cell22_470851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_470851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470851 prefixEnd_470851 := by exact prefixLift 470851
  have htrace : WordTrace (prefixWord ++ tailWord_470851) baseStart_470851 baseEnd_470851 := by
    simpa [prefixWord, tailWord_470851, baseEnd_470851] using wordTrace_append hprefix tailTrace_470851
  have hstable : (prefixWord ++ tailWord_470851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470851).length < 2 ^ (prefixWord ++ tailWord_470851).sum := by decide
  have hdescent : baseEnd_470851 < baseStart_470851 := by decide
  rcases family_descends (prefixWord ++ tailWord_470851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470930 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_470930 : Nat := 118140960795 + 470930 * 2 ^ 59
def prefixEnd_470930 : Nat := 4983230072969 + 3 ^ 40 * 470930 * 2
def baseEnd_470930 : Nat := 161208963081298478606159

theorem tailTrace_470930 : CollatzResearch.WordTrace tailWord_470930 prefixEnd_470930 161208963081298478606159 := by
  unfold tailWord_470930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294057045977128321468561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11450818789272342190582829 4294057045977128321468561)
  ·
    refine ⟨3220542784482846241101421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294057045977128321468561 3220542784482846241101421)
    ·
      refine ⟨1207703544181067340413033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3220542784482846241101421 1207703544181067340413033)
      ·
        refine ⟨905777658135800505309775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207703544181067340413033 905777658135800505309775)
        ·
          refine ⟨1358666487203700757964663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905777658135800505309775 1358666487203700757964663)
          ·
            refine ⟨2037999730805551136946995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358666487203700757964663 2037999730805551136946995)
            ·
              refine ⟨3056999596208326705420493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037999730805551136946995 3056999596208326705420493)
              ·
                refine ⟨1146374848578122514532685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056999596208326705420493 1146374848578122514532685)
                ·
                  refine ⟨429890568216795942949757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146374848578122514532685 429890568216795942949757)
                  ·
                    refine ⟨161208963081298478606159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429890568216795942949757 161208963081298478606159)
                    ·
                      rfl

theorem cell22_470930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_470930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470930 prefixEnd_470930 := by exact prefixLift 470930
  have htrace : WordTrace (prefixWord ++ tailWord_470930) baseStart_470930 baseEnd_470930 := by
    simpa [prefixWord, tailWord_470930, baseEnd_470930] using wordTrace_append hprefix tailTrace_470930
  have hstable : (prefixWord ++ tailWord_470930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470930).length < 2 ^ (prefixWord ++ tailWord_470930).sum := by decide
  have hdescent : baseEnd_470930 < baseStart_470930 := by decide
  rcases family_descends (prefixWord ++ tailWord_470930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470988 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_470988 : Nat := 118140960795 + 470988 * 2 ^ 59
def prefixEnd_470988 : Nat := 4983230072969 + 3 ^ 40 * 470988 * 2
def baseEnd_470988 : Nat := 53742939222201886885327

theorem tailTrace_470988 : CollatzResearch.WordTrace tailWord_470988 prefixEnd_470988 53742939222201886885327 := by
  unfold tailWord_470988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8589171808849194595742809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11452229078465592794323745 8589171808849194595742809)
  ·
    refine ⟨6441878856636895946807107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8589171808849194595742809 6441878856636895946807107)
    ·
      refine ⟨9662818284955343920210661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441878856636895946807107 9662818284955343920210661)
      ·
        refine ⟨1811778428429126985039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9662818284955343920210661 1811778428429126985039499)
        ·
          refine ⟨2717667642643690477559249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811778428429126985039499 2717667642643690477559249)
          ·
            refine ⟨2038250731982767858169437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717667642643690477559249 2038250731982767858169437)
            ·
              refine ⟨764344024493537946813539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2038250731982767858169437 764344024493537946813539)
              ·
                refine ⟨1146516036740306920220309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764344024493537946813539 1146516036740306920220309)
                ·
                  refine ⟨53742939222201886885327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1146516036740306920220309 53742939222201886885327)
                  ·
                    rfl

theorem cell22_470988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_470988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470988 prefixEnd_470988 := by exact prefixLift 470988
  have htrace : WordTrace (prefixWord ++ tailWord_470988) baseStart_470988 baseEnd_470988 := by
    simpa [prefixWord, tailWord_470988, baseEnd_470988] using wordTrace_append hprefix tailTrace_470988
  have hstable : (prefixWord ++ tailWord_470988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470988).length < 2 ^ (prefixWord ++ tailWord_470988).sum := by decide
  have hdescent : baseEnd_470988 < baseStart_470988 := by decide
  rcases family_descends (prefixWord ++ tailWord_470988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470994 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_470994 : Nat := 118140960795 + 470994 * 2 ^ 59
def prefixEnd_470994 : Nat := 4983230072969 + 3 ^ 40 * 470994 * 2
def baseEnd_470994 : Nat := 53743623863074548335321

theorem tailTrace_470994 : CollatzResearch.WordTrace tailWord_470994 prefixEnd_470994 53743623863074548335321 := by
  unfold tailWord_470994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294640613919163054051009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11452374970451101477469357 4294640613919163054051009)
  ·
    refine ⟨3220980460439372290538257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294640613919163054051009 3220980460439372290538257)
    ·
      refine ⟨2415735345329529217903693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220980460439372290538257 2415735345329529217903693)
      ·
        refine ⟨905900754498573456713885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2415735345329529217903693 905900754498573456713885)
        ·
          refine ⟨339712782936965046267707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905900754498573456713885 339712782936965046267707)
          ·
            refine ⟨509569174405447569401561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339712782936965046267707 509569174405447569401561)
            ·
              refine ⟨382176880804085677051171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509569174405447569401561 382176880804085677051171)
              ·
                refine ⟨573265321206128515576757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382176880804085677051171 573265321206128515576757)
                ·
                  refine ⟨53743623863074548335321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573265321206128515576757 53743623863074548335321)
                  ·
                    rfl

theorem cell22_470994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_470994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_470994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_470994 prefixEnd_470994 := by exact prefixLift 470994
  have htrace : WordTrace (prefixWord ++ tailWord_470994) baseStart_470994 baseEnd_470994 := by
    simpa [prefixWord, tailWord_470994, baseEnd_470994] using wordTrace_append hprefix tailTrace_470994
  have hstable : (prefixWord ++ tailWord_470994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470994).length < 2 ^ (prefixWord ++ tailWord_470994).sum := by decide
  have hdescent : baseEnd_470994 < baseStart_470994 := by decide
  rcases family_descends (prefixWord ++ tailWord_470994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471050 : List Nat := [3, 1, 2, 2, 4, 2, 1, 7]
def baseStart_471050 : Nat := 118140960795 + 471050 * 2 ^ 59
def prefixEnd_471050 : Nat := 4983230072969 + 3 ^ 40 * 471050 * 2
def baseEnd_471050 : Nat := 17916671281517573956199

theorem tailTrace_471050 : CollatzResearch.WordTrace tailWord_471050 prefixEnd_471050 17916671281517573956199 := by
  unfold tailWord_471050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295151235868443445060651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11453736628982515853495069 4295151235868443445060651)
  ·
    refine ⟨6442726853802665167590977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295151235868443445060651 6442726853802665167590977)
    ·
      refine ⟨4832045140351998875693233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6442726853802665167590977 4832045140351998875693233)
      ·
        refine ⟨3624033855263999156769925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4832045140351998875693233 3624033855263999156769925)
        ·
          refine ⟨679506347861999841894361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3624033855263999156769925 679506347861999841894361)
          ·
            refine ⟨509629760896499881420771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679506347861999841894361 509629760896499881420771)
            ·
              refine ⟨764444641344749822131157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509629760896499881420771 764444641344749822131157)
              ·
                refine ⟨17916671281517573956199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 764444641344749822131157 17916671281517573956199)
                ·
                  rfl

theorem cell22_471050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_471050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471050 prefixEnd_471050 := by exact prefixLift 471050
  have htrace : WordTrace (prefixWord ++ tailWord_471050) baseStart_471050 baseEnd_471050 := by
    simpa [prefixWord, tailWord_471050, baseEnd_471050] using wordTrace_append hprefix tailTrace_471050
  have hstable : (prefixWord ++ tailWord_471050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471050).length < 2 ^ (prefixWord ++ tailWord_471050).sum := by decide
  have hdescent : baseEnd_471050 < baseStart_471050 := by decide
  rcases family_descends (prefixWord ++ tailWord_471050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471093 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_471093 : Nat := 118140960795 + 471093 * 2 ^ 59
def prefixEnd_471093 : Nat := 4983230072969 + 3 ^ 40 * 471093 * 2
def baseEnd_471093 : Nat := 161264761312420386780659

theorem tailTrace_471093 : CollatzResearch.WordTrace tailWord_471093 prefixEnd_471093 161264761312420386780659 := by
  unfold tailWord_471093
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182173282317992124057933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11454782188211994749371955 17182173282317992124057933)
  ·
    refine ⟨6443314980869247046521725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17182173282317992124057933 6443314980869247046521725)
    ·
      refine ⟨2416243117825967642445647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6443314980869247046521725 2416243117825967642445647)
      ·
        refine ⟨3624364676738951463668471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416243117825967642445647 3624364676738951463668471)
        ·
          refine ⟨5436547015108427195502707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624364676738951463668471 5436547015108427195502707)
          ·
            refine ⟨8154820522662640793254061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436547015108427195502707 8154820522662640793254061)
            ·
              refine ⟨3058057695998490297470273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8154820522662640793254061 3058057695998490297470273)
              ·
                refine ⟨2293543271998867723102705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058057695998490297470273 2293543271998867723102705)
                ·
                  refine ⟨1720157453999150792327029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293543271998867723102705 1720157453999150792327029)
                  ·
                    refine ⟨161264761312420386780659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1720157453999150792327029 161264761312420386780659)
                    ·
                      rfl

theorem cell22_471093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_471093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471093 prefixEnd_471093 := by exact prefixLift 471093
  have htrace : WordTrace (prefixWord ++ tailWord_471093) baseStart_471093 baseEnd_471093 := by
    simpa [prefixWord, tailWord_471093, baseEnd_471093] using wordTrace_append hprefix tailTrace_471093
  have hstable : (prefixWord ++ tailWord_471093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471093).length < 2 ^ (prefixWord ++ tailWord_471093).sum := by decide
  have hdescent : baseEnd_471093 < baseStart_471093 := by decide
  rcases family_descends (prefixWord ++ tailWord_471093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471125 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_471125 : Nat := 118140960795 + 471125 * 2 ^ 59
def prefixEnd_471125 : Nat := 4983230072969 + 3 ^ 40 * 471125 * 2
def baseEnd_471125 : Nat := 161275715566382969980561

theorem tailTrace_471125 : CollatzResearch.WordTrace tailWord_471125 prefixEnd_471125 161275715566382969980561 := by
  unfold tailWord_471125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183340418202061589222829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11455560278801374392815219 17183340418202061589222829)
  ·
    refine ⟨6443752656825773095958561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17183340418202061589222829 6443752656825773095958561)
    ·
      refine ⟨4832814492619329821968921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6443752656825773095958561 4832814492619329821968921)
      ·
        refine ⟨3624610869464497366476691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4832814492619329821968921 3624610869464497366476691)
        ·
          refine ⟨5436916304196746049715037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624610869464497366476691 5436916304196746049715037)
          ·
            refine ⟨2038843614073779768643139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5436916304196746049715037 2038843614073779768643139)
            ·
              refine ⟨3058265421110669652964709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038843614073779768643139 3058265421110669652964709)
              ·
                refine ⟨573424766458250559930883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3058265421110669652964709 573424766458250559930883)
                ·
                  refine ⟨860137149687375839896325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573424766458250559930883 860137149687375839896325)
                  ·
                    refine ⟨161275715566382969980561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860137149687375839896325 161275715566382969980561)
                    ·
                      rfl

theorem cell22_471125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_471125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471125 prefixEnd_471125 := by exact prefixLift 471125
  have htrace : WordTrace (prefixWord ++ tailWord_471125) baseStart_471125 baseEnd_471125 := by
    simpa [prefixWord, tailWord_471125, baseEnd_471125] using wordTrace_append hprefix tailTrace_471125
  have hstable : (prefixWord ++ tailWord_471125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471125).length < 2 ^ (prefixWord ++ tailWord_471125).sum := by decide
  have hdescent : baseEnd_471125 < baseStart_471125 := by decide
  rcases family_descends (prefixWord ++ tailWord_471125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471172 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_471172 : Nat := 118140960795 + 471172 * 2 ^ 59
def prefixEnd_471172 : Nat := 4983230072969 + 3 ^ 40 * 471172 * 2
def baseEnd_471172 : Nat := 161291804626890514055417

theorem tailTrace_471172 : CollatzResearch.WordTrace tailWord_471172 prefixEnd_471172 161291804626890514055417 := by
  unfold tailWord_471172
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592527324515894308091885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11456703099354525744122513 8592527324515894308091885)
  ·
    refine ⟨3222197746693460365534457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8592527324515894308091885 3222197746693460365534457)
    ·
      refine ⟨2416648310020095274150843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3222197746693460365534457 2416648310020095274150843)
      ·
        refine ⟨3624972465030142911226265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416648310020095274150843 3624972465030142911226265)
        ·
          refine ⟨2718729348772607183419699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624972465030142911226265 2718729348772607183419699)
          ·
            refine ⟨4078094023158910775129549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718729348772607183419699 4078094023158910775129549)
            ·
              refine ⟨1529285258684591540673581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4078094023158910775129549 1529285258684591540673581)
              ·
                refine ⟨573481972006721827752593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1529285258684591540673581 573481972006721827752593)
                ·
                  refine ⟨430111479005041370814445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573481972006721827752593 430111479005041370814445)
                  ·
                    refine ⟨161291804626890514055417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430111479005041370814445 161291804626890514055417)
                    ·
                      rfl

theorem cell22_471172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_471172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471172 prefixEnd_471172 := by exact prefixLift 471172
  have htrace : WordTrace (prefixWord ++ tailWord_471172) baseStart_471172 baseEnd_471172 := by
    simpa [prefixWord, tailWord_471172, baseEnd_471172] using wordTrace_append hprefix tailTrace_471172
  have hstable : (prefixWord ++ tailWord_471172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471172).length < 2 ^ (prefixWord ++ tailWord_471172).sum := by decide
  have hdescent : baseEnd_471172 < baseStart_471172 := by decide
  rcases family_descends (prefixWord ++ tailWord_471172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471275 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 6]
def baseStart_471275 : Nat := 118140960795 + 471275 * 2 ^ 59
def prefixEnd_471275 : Nat := 4983230072969 + 3 ^ 40 * 471275 * 2
def baseEnd_471275 : Nat := 53775687877277526243367

theorem tailTrace_471275 : CollatzResearch.WordTrace tailWord_471275 prefixEnd_471275 53775687877277526243367 := by
  unfold tailWord_471275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188811367658637207183279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11459207578439091471455519 17188811367658637207183279)
  ·
    refine ⟨25783217051487955810774919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17188811367658637207183279 25783217051487955810774919)
    ·
      refine ⟨38674825577231933716162379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25783217051487955810774919 38674825577231933716162379)
      ·
        refine ⟨58012238365847900574243569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38674825577231933716162379 58012238365847900574243569)
        ·
          refine ⟨43509178774385925430682677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58012238365847900574243569 43509178774385925430682677)
          ·
            refine ⟨4078985510098680509126501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43509178774385925430682677 4078985510098680509126501)
            ·
              refine ⟨764809783143502595461219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4078985510098680509126501 764809783143502595461219)
              ·
                refine ⟨1147214674715253893191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764809783143502595461219 1147214674715253893191829)
                ·
                  refine ⟨53775687877277526243367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1147214674715253893191829 53775687877277526243367)
                  ·
                    rfl

theorem cell22_471275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_471275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471275 prefixEnd_471275 := by exact prefixLift 471275
  have htrace : WordTrace (prefixWord ++ tailWord_471275) baseStart_471275 baseEnd_471275 := by
    simpa [prefixWord, tailWord_471275, baseEnd_471275] using wordTrace_append hprefix tailTrace_471275
  have hstable : (prefixWord ++ tailWord_471275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471275).length < 2 ^ (prefixWord ++ tailWord_471275).sum := by decide
  have hdescent : baseEnd_471275 < baseStart_471275 := by decide
  rcases family_descends (prefixWord ++ tailWord_471275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471294 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_471294 : Nat := 118140960795 + 471294 * 2 ^ 59
def prefixEnd_471294 : Nat := 4983230072969 + 3 ^ 40 * 471294 * 2
def baseEnd_471294 : Nat := 161333567720122862505043

theorem tailTrace_471294 : CollatzResearch.WordTrace tailWord_471294 prefixEnd_471294 161333567720122862505043 := by
  unfold tailWord_471294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148688044323725431515617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11459669569726535634749957 2148688044323725431515617)
  ·
    refine ⟨1611516033242794073636713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2148688044323725431515617 1611516033242794073636713)
    ·
      refine ⟨1208637024932095555227535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1611516033242794073636713 1208637024932095555227535)
      ·
        refine ⟨1812955537398143332841303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208637024932095555227535 1812955537398143332841303)
        ·
          refine ⟨2719433306097214999261955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812955537398143332841303 2719433306097214999261955)
          ·
            refine ⟨4079149959145822498892933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719433306097214999261955 4079149959145822498892933)
            ·
              refine ⟨764840617339841718542425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4079149959145822498892933 764840617339841718542425)
              ·
                refine ⟨573630463004881288906819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764840617339841718542425 573630463004881288906819)
                ·
                  refine ⟨860445694507321933360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573630463004881288906819 860445694507321933360229)
                  ·
                    refine ⟨161333567720122862505043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860445694507321933360229 161333567720122862505043)
                    ·
                      rfl

theorem cell22_471294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_471294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471294 prefixEnd_471294 := by exact prefixLift 471294
  have htrace : WordTrace (prefixWord ++ tailWord_471294) baseStart_471294 baseEnd_471294 := by
    simpa [prefixWord, tailWord_471294, baseEnd_471294] using wordTrace_append hprefix tailTrace_471294
  have hstable : (prefixWord ++ tailWord_471294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471294).length < 2 ^ (prefixWord ++ tailWord_471294).sum := by decide
  have hdescent : baseEnd_471294 < baseStart_471294 := by decide
  rcases family_descends (prefixWord ++ tailWord_471294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471305 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_471305 : Nat := 118140960795 + 471305 * 2 ^ 59
def prefixEnd_471305 : Nat := 4983230072969 + 3 ^ 40 * 471305 * 2
def baseEnd_471305 : Nat := 161337333244922500480009

theorem tailTrace_471305 : CollatzResearch.WordTrace tailWord_471305 prefixEnd_471305 161337333244922500480009 := by
  unfold tailWord_471305
  simp only [CollatzResearch.WordTrace]
  refine ⟨17189905557549952330775369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11459937038366634887183579 17189905557549952330775369)
  ·
    refine ⟨12892429168162464248081527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17189905557549952330775369 12892429168162464248081527)
    ·
      refine ⟨19338643752243696372122291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892429168162464248081527 19338643752243696372122291)
      ·
        refine ⟨29007965628365544558183437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338643752243696372122291 29007965628365544558183437)
        ·
          refine ⟨10877987110637079209318789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29007965628365544558183437 10877987110637079209318789)
          ·
            refine ⟨2039622583244452351747273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10877987110637079209318789 2039622583244452351747273)
            ·
              refine ⟨1529716937433339263810455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039622583244452351747273 1529716937433339263810455)
              ·
                refine ⟨2294575406150008895715683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529716937433339263810455 2294575406150008895715683)
                ·
                  refine ⟨3441863109225013343573525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294575406150008895715683 3441863109225013343573525)
                  ·
                    refine ⟨161337333244922500480009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3441863109225013343573525 161337333244922500480009)
                    ·
                      rfl

theorem cell22_471305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_471305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471305 prefixEnd_471305 := by exact prefixLift 471305
  have htrace : WordTrace (prefixWord ++ tailWord_471305) baseStart_471305 baseEnd_471305 := by
    simpa [prefixWord, tailWord_471305, baseEnd_471305] using wordTrace_append hprefix tailTrace_471305
  have hstable : (prefixWord ++ tailWord_471305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471305).length < 2 ^ (prefixWord ++ tailWord_471305).sum := by decide
  have hdescent : baseEnd_471305 < baseStart_471305 := by decide
  rcases family_descends (prefixWord ++ tailWord_471305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471326 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_471326 : Nat := 118140960795 + 471326 * 2 ^ 59
def prefixEnd_471326 : Nat := 4983230072969 + 3 ^ 40 * 471326 * 2
def baseEnd_471326 : Nat := 53781507324695148568315

theorem tailTrace_471326 : CollatzResearch.WordTrace tailWord_471326 prefixEnd_471326 53781507324695148568315 := by
  unfold tailWord_471326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148833936309234114661229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11460447660315915278193221 2148833936309234114661229)
  ·
    refine ⟨805812726115962792997961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2148833936309234114661229 805812726115962792997961)
    ·
      refine ⟨604359544586972094748471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805812726115962792997961 604359544586972094748471)
      ·
        refine ⟨906539316880458142122707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604359544586972094748471 906539316880458142122707)
        ·
          refine ⟨1359808975320687213184061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906539316880458142122707 1359808975320687213184061)
          ·
            refine ⟨509928365745257704944023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1359808975320687213184061 509928365745257704944023)
            ·
              refine ⟨764892548617886557416035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509928365745257704944023 764892548617886557416035)
              ·
                refine ⟨1147338822926829836124053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764892548617886557416035 1147338822926829836124053)
                ·
                  refine ⟨53781507324695148568315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1147338822926829836124053 53781507324695148568315)
                  ·
                    rfl

theorem cell22_471326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_471326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471326 prefixEnd_471326 := by exact prefixLift 471326
  have htrace : WordTrace (prefixWord ++ tailWord_471326) baseStart_471326 baseEnd_471326 := by
    simpa [prefixWord, tailWord_471326, baseEnd_471326] using wordTrace_append hprefix tailTrace_471326
  have hstable : (prefixWord ++ tailWord_471326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471326).length < 2 ^ (prefixWord ++ tailWord_471326).sum := by decide
  have hdescent : baseEnd_471326 < baseStart_471326 := by decide
  rcases family_descends (prefixWord ++ tailWord_471326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471352 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_471352 : Nat := 118140960795 + 471352 * 2 ^ 59
def prefixEnd_471352 : Nat := 4983230072969 + 3 ^ 40 * 471352 * 2
def baseEnd_471352 : Nat := 161353422305430044554865

theorem tailTrace_471352 : CollatzResearch.WordTrace tailWord_471352 prefixEnd_471352 161353422305430044554865 := by
  unfold tailWord_471352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595809894189839678868155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11461079858919786238490873 8595809894189839678868155)
  ·
    refine ⟨12893714841284759518302233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595809894189839678868155 12893714841284759518302233)
    ·
      refine ⟨9670286130963569638726675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12893714841284759518302233 9670286130963569638726675)
      ·
        refine ⟨14505429196445354458090013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670286130963569638726675 14505429196445354458090013)
        ·
          refine ⟨5439535948667007921783755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14505429196445354458090013 5439535948667007921783755)
          ·
            refine ⟨8159303923000511882675633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439535948667007921783755 8159303923000511882675633)
            ·
              refine ⟨6119477942250383912006725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8159303923000511882675633 6119477942250383912006725)
              ·
                refine ⟨1147402114171946983501261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6119477942250383912006725 1147402114171946983501261)
                ·
                  refine ⟨430275792814480118812973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147402114171946983501261 430275792814480118812973)
                  ·
                    refine ⟨161353422305430044554865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430275792814480118812973 161353422305430044554865)
                    ·
                      rfl

theorem cell22_471352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_471352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471352 prefixEnd_471352 := by exact prefixLift 471352
  have htrace : WordTrace (prefixWord ++ tailWord_471352) baseStart_471352 baseEnd_471352 := by
    simpa [prefixWord, tailWord_471352, baseEnd_471352] using wordTrace_append hprefix tailTrace_471352
  have hstable : (prefixWord ++ tailWord_471352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471352).length < 2 ^ (prefixWord ++ tailWord_471352).sum := by decide
  have hdescent : baseEnd_471352 < baseStart_471352 := by decide
  rcases family_descends (prefixWord ++ tailWord_471352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471369 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_471369 : Nat := 118140960795 + 471369 * 2 ^ 59
def prefixEnd_471369 : Nat := 4983230072969 + 3 ^ 40 * 471369 * 2
def baseEnd_471369 : Nat := 161359241752847666879813

theorem tailTrace_471369 : CollatzResearch.WordTrace tailWord_471369 prefixEnd_471369 161359241752847666879813 := by
  unfold tailWord_471369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192239829318091261105161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11461493219545394174070107 17192239829318091261105161)
  ·
    refine ⟨12894179871988568445828871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17192239829318091261105161 12894179871988568445828871)
    ·
      refine ⟨19341269807982852668743307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12894179871988568445828871 19341269807982852668743307)
      ·
        refine ⟨29011904711974279003114961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19341269807982852668743307 29011904711974279003114961)
        ·
          refine ⟨21758928533980709252336221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29011904711974279003114961 21758928533980709252336221)
          ·
            refine ⟨8159598200242765969626083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21758928533980709252336221 8159598200242765969626083)
            ·
              refine ⟨12239397300364148954439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159598200242765969626083 12239397300364148954439125)
              ·
                refine ⟨286860874227284741119667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12239397300364148954439125 286860874227284741119667)
                ·
                  refine ⟨430291311340927111679501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286860874227284741119667 430291311340927111679501)
                  ·
                    refine ⟨161359241752847666879813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430291311340927111679501 161359241752847666879813)
                    ·
                      rfl

theorem cell22_471369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_471369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471369 prefixEnd_471369 := by exact prefixLift 471369
  have htrace : WordTrace (prefixWord ++ tailWord_471369) baseStart_471369 baseEnd_471369 := by
    simpa [prefixWord, tailWord_471369, baseEnd_471369] using wordTrace_append hprefix tailTrace_471369
  have hstable : (prefixWord ++ tailWord_471369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471369).length < 2 ^ (prefixWord ++ tailWord_471369).sum := by decide
  have hdescent : baseEnd_471369 < baseStart_471369 := by decide
  rcases family_descends (prefixWord ++ tailWord_471369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471397 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_471397 : Nat := 118140960795 + 471397 * 2 ^ 59
def prefixEnd_471397 : Nat := 4983230072969 + 3 ^ 40 * 471397 * 2
def baseEnd_471397 : Nat := 161368826725064927179727

theorem tailTrace_471397 : CollatzResearch.WordTrace tailWord_471397 prefixEnd_471397 161368826725064927179727 := by
  unfold tailWord_471397
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193261073216652043124445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11462174048811101362082963 17193261073216652043124445)
  ·
    refine ⟨6447472902456244516171667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17193261073216652043124445 6447472902456244516171667)
    ·
      refine ⟨9671209353684366774257501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447472902456244516171667 9671209353684366774257501)
      ·
        refine ⟨3626703507631637540346563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9671209353684366774257501 3626703507631637540346563)
        ·
          refine ⟨5440055261447456310519845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626703507631637540346563 5440055261447456310519845)
          ·
            refine ⟨1020010361521398058222471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5440055261447456310519845 1020010361521398058222471)
            ·
              refine ⟨1530015542282097087333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020010361521398058222471 1530015542282097087333707)
              ·
                refine ⟨2295023313423145631000561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530015542282097087333707 2295023313423145631000561)
                ·
                  refine ⟨1721267485067359223250421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295023313423145631000561 1721267485067359223250421)
                  ·
                    refine ⟨161368826725064927179727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1721267485067359223250421 161368826725064927179727)
                    ·
                      rfl

theorem cell22_471397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_471397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471397 prefixEnd_471397 := by exact prefixLift 471397
  have htrace : WordTrace (prefixWord ++ tailWord_471397) baseStart_471397 baseEnd_471397 := by
    simpa [prefixWord, tailWord_471397, baseEnd_471397] using wordTrace_append hprefix tailTrace_471397
  have hstable : (prefixWord ++ tailWord_471397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471397).length < 2 ^ (prefixWord ++ tailWord_471397).sum := by decide
  have hdescent : baseEnd_471397 < baseStart_471397 := by decide
  rcases family_descends (prefixWord ++ tailWord_471397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471440 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_471440 : Nat := 118140960795 + 471440 * 2 ^ 59
def prefixEnd_471440 : Nat := 4983230072969 + 3 ^ 40 * 471440 * 2
def baseEnd_471440 : Nat := 161383546503827148354595

theorem tailTrace_471440 : CollatzResearch.WordTrace tailWord_471440 prefixEnd_471440 161383546503827148354595 := by
  unfold tailWord_471440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597414706030435193469887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11463219608040580257959849 8597414706030435193469887)
  ·
    refine ⟨12896122059045652790204831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8597414706030435193469887 12896122059045652790204831)
    ·
      refine ⟨19344183088568479185307247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12896122059045652790204831 19344183088568479185307247)
      ·
        refine ⟨29016274632852718777960871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344183088568479185307247 29016274632852718777960871)
        ·
          refine ⟨43524411949279078166941307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29016274632852718777960871 43524411949279078166941307)
          ·
            refine ⟨65286617923918617250411961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43524411949279078166941307 65286617923918617250411961)
            ·
              refine ⟨48964963442938962937808971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65286617923918617250411961 48964963442938962937808971)
              ·
                refine ⟨73447445164408444406713457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48964963442938962937808971 73447445164408444406713457)
                ·
                  refine ⟨55085583873306333305035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73447445164408444406713457 55085583873306333305035093)
                  ·
                    refine ⟨161383546503827148354595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 55085583873306333305035093 161383546503827148354595)
                    ·
                      rfl

theorem cell22_471440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_471440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471440 prefixEnd_471440 := by exact prefixLift 471440
  have htrace : WordTrace (prefixWord ++ tailWord_471440) baseStart_471440 baseEnd_471440 := by
    simpa [prefixWord, tailWord_471440, baseEnd_471440] using wordTrace_append hprefix tailTrace_471440
  have hstable : (prefixWord ++ tailWord_471440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471440).length < 2 ^ (prefixWord ++ tailWord_471440).sum := by decide
  have hdescent : baseEnd_471440 < baseStart_471440 := by decide
  rcases family_descends (prefixWord ++ tailWord_471440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471459 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 5]
def baseStart_471459 : Nat := 118140960795 + 471459 * 2 ^ 59
def prefixEnd_471459 : Nat := 4983230072969 + 3 ^ 40 * 471459 * 2
def baseEnd_471459 : Nat := 161390050592117432129537

theorem tailTrace_471459 : CollatzResearch.WordTrace tailWord_471459 prefixEnd_471459 161390050592117432129537 := by
  unfold tailWord_471459
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195522398992036631881431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11463681599328024421254287 17195522398992036631881431)
  ·
    refine ⟨25793283598488054947822147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195522398992036631881431 25793283598488054947822147)
    ·
      refine ⟨38689925397732082421733221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25793283598488054947822147 38689925397732082421733221)
      ·
        refine ⟨7254361012074765454074979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38689925397732082421733221 7254361012074765454074979)
        ·
          refine ⟨10881541518112148181112469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254361012074765454074979 10881541518112148181112469)
          ·
            refine ⟨510072258661506945989647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10881541518112148181112469 510072258661506945989647)
            ·
              refine ⟨765108387992260418984471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510072258661506945989647 765108387992260418984471)
              ·
                refine ⟨1147662581988390628476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765108387992260418984471 1147662581988390628476707)
                ·
                  refine ⟨1721493872982585942715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147662581988390628476707 1721493872982585942715061)
                  ·
                    refine ⟨161390050592117432129537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1721493872982585942715061 161390050592117432129537)
                    ·
                      rfl

theorem cell22_471459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].length) (baseStart_471459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471459 prefixEnd_471459 := by exact prefixLift 471459
  have htrace : WordTrace (prefixWord ++ tailWord_471459) baseStart_471459 baseEnd_471459 := by
    simpa [prefixWord, tailWord_471459, baseEnd_471459] using wordTrace_append hprefix tailTrace_471459
  have hstable : (prefixWord ++ tailWord_471459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471459).length < 2 ^ (prefixWord ++ tailWord_471459).sum := by decide
  have hdescent : baseEnd_471459 < baseStart_471459 := by decide
  rcases family_descends (prefixWord ++ tailWord_471459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471502 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_471502 : Nat := 118140960795 + 471502 * 2 ^ 59
def prefixEnd_471502 : Nat := 4983230072969 + 3 ^ 40 * 471502 * 2
def baseEnd_471502 : Nat := 161404770370879653304405

theorem tailTrace_471502 : CollatzResearch.WordTrace tailWord_471502 prefixEnd_471502 161404770370879653304405 := by
  unfold tailWord_471502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149636342229531871962095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11464727158557503317131173 2149636342229531871962095)
  ·
    refine ⟨3224454513344297807943143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149636342229531871962095 3224454513344297807943143)
    ·
      refine ⟨4836681770016446711914715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224454513344297807943143 4836681770016446711914715)
      ·
        refine ⟨7255022655024670067872073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836681770016446711914715 7255022655024670067872073)
        ·
          refine ⟨5441266991268502550904055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255022655024670067872073 5441266991268502550904055)
          ·
            refine ⟨8161900486902753826356083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441266991268502550904055 8161900486902753826356083)
            ·
              refine ⟨12242850730354130739534125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161900486902753826356083 12242850730354130739534125)
              ·
                refine ⟨4591069023882799027325297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12242850730354130739534125 4591069023882799027325297)
                ·
                  refine ⟨3443301767912099270493973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591069023882799027325297 3443301767912099270493973)
                  ·
                    refine ⟨161404770370879653304405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3443301767912099270493973 161404770370879653304405)
                    ·
                      rfl

theorem cell22_471502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_471502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471502 prefixEnd_471502 := by exact prefixLift 471502
  have htrace : WordTrace (prefixWord ++ tailWord_471502) baseStart_471502 baseEnd_471502 := by
    simpa [prefixWord, tailWord_471502, baseEnd_471502] using wordTrace_append hprefix tailTrace_471502
  have hstable : (prefixWord ++ tailWord_471502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471502).length < 2 ^ (prefixWord ++ tailWord_471502).sum := by decide
  have hdescent : baseEnd_471502 < baseStart_471502 := by decide
  rcases family_descends (prefixWord ++ tailWord_471502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471506 : List Nat := [3, 2, 2, 4, 1, 1, 2, 7]
def baseStart_471506 : Nat := 118140960795 + 471506 * 2 ^ 59
def prefixEnd_471506 : Nat := 4983230072969 + 3 ^ 40 * 471506 * 2
def baseEnd_471506 : Nat := 17934015516958330689377

theorem tailTrace_471506 : CollatzResearch.WordTrace tailWord_471506 prefixEnd_471506 17934015516958330689377 := by
  unfold tailWord_471506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299309157455440914710593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11464824419881175772561581 4299309157455440914710593)
  ·
    refine ⟨3224481868091580686032945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299309157455440914710593 3224481868091580686032945)
    ·
      refine ⟨2418361401068685514524709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3224481868091580686032945 2418361401068685514524709)
      ·
        refine ⟨453442762700378533973383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2418361401068685514524709 453442762700378533973383)
        ·
          refine ⟨680164144050567800960075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453442762700378533973383 680164144050567800960075)
          ·
            refine ⟨1020246216075851701440113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680164144050567800960075 1020246216075851701440113)
            ·
              refine ⟨765184662056888776080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020246216075851701440113 765184662056888776080085)
              ·
                refine ⟨17934015516958330689377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 765184662056888776080085 17934015516958330689377)
                ·
                  rfl

theorem cell22_471506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_471506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471506 prefixEnd_471506 := by exact prefixLift 471506
  have htrace : WordTrace (prefixWord ++ tailWord_471506) baseStart_471506 baseEnd_471506 := by
    simpa [prefixWord, tailWord_471506, baseEnd_471506] using wordTrace_append hprefix tailTrace_471506
  have hstable : (prefixWord ++ tailWord_471506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471506).length < 2 ^ (prefixWord ++ tailWord_471506).sum := by decide
  have hdescent : baseEnd_471506 < baseStart_471506 := by decide
  rcases family_descends (prefixWord ++ tailWord_471506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471547 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_471547 : Nat := 118140960795 + 471547 * 2 ^ 59
def prefixEnd_471547 : Nat := 4983230072969 + 3 ^ 40 * 471547 * 2
def baseEnd_471547 : Nat := 161420174790514535929267

theorem tailTrace_471547 : CollatzResearch.WordTrace tailWord_471547 prefixEnd_471547 161420174790514535929267 := by
  unfold tailWord_471547
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198732022673227661084895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11465821348448818440723263 17198732022673227661084895)
  ·
    refine ⟨25798098034009841491627343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198732022673227661084895 25798098034009841491627343)
    ·
      refine ⟨38697147051014762237441015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25798098034009841491627343 38697147051014762237441015)
      ·
        refine ⟨58045720576522143356161523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38697147051014762237441015 58045720576522143356161523)
        ·
          refine ⟨87068580864783215034242285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58045720576522143356161523 87068580864783215034242285)
          ·
            refine ⟨32650717824293705637840857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87068580864783215034242285 32650717824293705637840857)
            ·
              refine ⟨24488038368220279228380643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32650717824293705637840857 24488038368220279228380643)
              ·
                refine ⟨36732057552330418842570965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24488038368220279228380643 36732057552330418842570965)
                ·
                  refine ⟨860907598882744191622757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 36732057552330418842570965 860907598882744191622757)
                  ·
                    refine ⟨161420174790514535929267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860907598882744191622757 161420174790514535929267)
                    ·
                      rfl

theorem cell22_471547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_471547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471547 prefixEnd_471547 := by exact prefixLift 471547
  have htrace : WordTrace (prefixWord ++ tailWord_471547) baseStart_471547 baseEnd_471547 := by
    simpa [prefixWord, tailWord_471547, baseEnd_471547] using wordTrace_append hprefix tailTrace_471547
  have hstable : (prefixWord ++ tailWord_471547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471547).length < 2 ^ (prefixWord ++ tailWord_471547).sum := by decide
  have hdescent : baseEnd_471547 < baseStart_471547 := by decide
  rcases family_descends (prefixWord ++ tailWord_471547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471564 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_471564 : Nat := 118140960795 + 471564 * 2 ^ 59
def prefixEnd_471564 : Nat := 4983230072969 + 3 ^ 40 * 471564 * 2
def baseEnd_471564 : Nat := 161425994237932158254215

theorem tailTrace_471564 : CollatzResearch.WordTrace tailWord_471564 prefixEnd_471564 161425994237932158254215 := by
  unfold tailWord_471564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599676031805819782226873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11466234709074426376302497 8599676031805819782226873)
  ·
    refine ⟨6449757023854364836670155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8599676031805819782226873 6449757023854364836670155)
    ·
      refine ⟨9674635535781547255005233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449757023854364836670155 9674635535781547255005233)
      ·
        refine ⟨7255976651836160441253925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9674635535781547255005233 7255976651836160441253925)
        ·
          refine ⟨1360495622219280082735111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7255976651836160441253925 1360495622219280082735111)
          ·
            refine ⟨2040743433328920124102667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360495622219280082735111 2040743433328920124102667)
            ·
              refine ⟨3061115149993380186154001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040743433328920124102667 3061115149993380186154001)
              ·
                refine ⟨2295836362495035139615501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061115149993380186154001 2295836362495035139615501)
                ·
                  refine ⟨860938635935638177355813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2295836362495035139615501 860938635935638177355813)
                  ·
                    refine ⟨161425994237932158254215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 860938635935638177355813 161425994237932158254215)
                    ·
                      rfl

theorem cell22_471564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_471564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471564 prefixEnd_471564 := by exact prefixLift 471564
  have htrace : WordTrace (prefixWord ++ tailWord_471564) baseStart_471564 baseEnd_471564 := by
    simpa [prefixWord, tailWord_471564, baseEnd_471564] using wordTrace_append hprefix tailTrace_471564
  have hstable : (prefixWord ++ tailWord_471564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471564).length < 2 ^ (prefixWord ++ tailWord_471564).sum := by decide
  have hdescent : baseEnd_471564 < baseStart_471564 := by decide
  rcases family_descends (prefixWord ++ tailWord_471564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471577 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_471577 : Nat := 118140960795 + 471577 * 2 ^ 59
def prefixEnd_471577 : Nat := 4983230072969 + 3 ^ 40 * 471577 * 2
def baseEnd_471577 : Nat := 161430444403604457679175

theorem tailTrace_471577 : CollatzResearch.WordTrace tailWord_471577 prefixEnd_471577 161430444403604457679175 := by
  unfold tailWord_471577
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199826212564542784676985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11466550808376361856451323 17199826212564542784676985)
  ·
    refine ⟨12899869659423407088507739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17199826212564542784676985 12899869659423407088507739)
    ·
      refine ⟨19349804489135110632761609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12899869659423407088507739 19349804489135110632761609)
      ·
        refine ⟨14512353366851332974571207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19349804489135110632761609 14512353366851332974571207)
        ·
          refine ⟨21768530050276999461856811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512353366851332974571207 21768530050276999461856811)
          ·
            refine ⟨32652795075415499192785217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768530050276999461856811 32652795075415499192785217)
            ·
              refine ⟨24489596306561624394588913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32652795075415499192785217 24489596306561624394588913)
              ·
                refine ⟨18367197229921218295941685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24489596306561624394588913 18367197229921218295941685)
                ·
                  refine ⟨1721924740305114215244533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18367197229921218295941685 1721924740305114215244533)
                  ·
                    refine ⟨161430444403604457679175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1721924740305114215244533 161430444403604457679175)
                    ·
                      rfl

theorem cell22_471577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_471577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471577 prefixEnd_471577 := by exact prefixLift 471577
  have htrace : WordTrace (prefixWord ++ tailWord_471577) baseStart_471577 baseEnd_471577 := by
    simpa [prefixWord, tailWord_471577, baseEnd_471577] using wordTrace_append hprefix tailTrace_471577
  have hstable : (prefixWord ++ tailWord_471577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471577).length < 2 ^ (prefixWord ++ tailWord_471577).sum := by decide
  have hdescent : baseEnd_471577 < baseStart_471577 := by decide
  rcases family_descends (prefixWord ++ tailWord_471577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471598 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_471598 : Nat := 118140960795 + 471598 * 2 ^ 59
def prefixEnd_471598 : Nat := 4983230072969 + 3 ^ 40 * 471598 * 2
def baseEnd_471598 : Nat := 161437633132767402904111

theorem tailTrace_471598 : CollatzResearch.WordTrace tailWord_471598 prefixEnd_471598 161437633132767402904111 := by
  unfold tailWord_471598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150074018186057921398931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11467061430325642247460965 2150074018186057921398931)
  ·
    refine ⟨3225111027279086882098397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150074018186057921398931 3225111027279086882098397)
    ·
      refine ⟨1209416635229657580786899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3225111027279086882098397 1209416635229657580786899)
      ·
        refine ⟨1814124952844486371180349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209416635229657580786899 1814124952844486371180349)
        ·
          refine ⟨680296857316682389192631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1814124952844486371180349 680296857316682389192631)
          ·
            refine ⟨1020445285975023583788947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680296857316682389192631 1020445285975023583788947)
            ·
              refine ⟨1530667928962535375683421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020445285975023583788947 1530667928962535375683421)
              ·
                refine ⟨574000473360950765881283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530667928962535375683421 574000473360950765881283)
                ·
                  refine ⟨861000710041426148821925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574000473360950765881283 861000710041426148821925)
                  ·
                    refine ⟨161437633132767402904111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861000710041426148821925 161437633132767402904111)
                    ·
                      rfl

theorem cell22_471598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_471598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471598 prefixEnd_471598 := by exact prefixLift 471598
  have htrace : WordTrace (prefixWord ++ tailWord_471598) baseStart_471598 baseEnd_471598 := by
    simpa [prefixWord, tailWord_471598, baseEnd_471598] using wordTrace_append hprefix tailTrace_471598
  have hstable : (prefixWord ++ tailWord_471598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471598).length < 2 ^ (prefixWord ++ tailWord_471598).sum := by decide
  have hdescent : baseEnd_471598 < baseStart_471598 := by decide
  rcases family_descends (prefixWord ++ tailWord_471598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471607 : List Nat := [1, 1, 3, 1, 2, 3, 11]
def baseStart_471607 : Nat := 118140960795 + 471607 * 2 ^ 59
def prefixEnd_471607 : Nat := 4983230072969 + 3 ^ 40 * 471607 * 2
def baseEnd_471607 : Nat := 5979285704322014052929

theorem tailTrace_471607 : CollatzResearch.WordTrace tailWord_471607 prefixEnd_471607 5979285704322014052929 := by
  unfold tailWord_471607
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200920402455857908269075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11467280268303905272179383 17200920402455857908269075)
  ·
    refine ⟨25801380603683786862403613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17200920402455857908269075 25801380603683786862403613)
    ·
      refine ⟨9675517726381420073401355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25801380603683786862403613 9675517726381420073401355)
      ·
        refine ⟨14513276589572130110102033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675517726381420073401355 14513276589572130110102033)
        ·
          refine ⟨10884957442179097582576525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14513276589572130110102033 10884957442179097582576525)
          ·
            refine ⟨4081859040817161593466197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10884957442179097582576525 4081859040817161593466197)
            ·
              refine ⟨5979285704322014052929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4081859040817161593466197 5979285704322014052929)
              ·
                rfl

theorem cell22_471607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 11].length) (baseStart_471607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471607 prefixEnd_471607 := by exact prefixLift 471607
  have htrace : WordTrace (prefixWord ++ tailWord_471607) baseStart_471607 baseEnd_471607 := by
    simpa [prefixWord, tailWord_471607, baseEnd_471607] using wordTrace_append hprefix tailTrace_471607
  have hstable : (prefixWord ++ tailWord_471607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471607).length < 2 ^ (prefixWord ++ tailWord_471607).sum := by decide
  have hdescent : baseEnd_471607 < baseStart_471607 := by decide
  rcases family_descends (prefixWord ++ tailWord_471607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471609 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_471609 : Nat := 118140960795 + 471609 * 2 ^ 59
def prefixEnd_471609 : Nat := 4983230072969 + 3 ^ 40 * 471609 * 2
def baseEnd_471609 : Nat := 161441398657567040879077

theorem tailTrace_471609 : CollatzResearch.WordTrace tailWord_471609 prefixEnd_471609 161441398657567040879077 := by
  unfold tailWord_471609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200993348448612249841881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11467328898965741499894587 17200993348448612249841881)
  ·
    refine ⟨12900745011336459187381411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17200993348448612249841881 12900745011336459187381411)
    ·
      refine ⟨19351117517004688781072117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12900745011336459187381411 19351117517004688781072117)
      ·
        refine ⟨1814167267219189573225511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19351117517004688781072117 1814167267219189573225511)
        ·
          refine ⟨2721250900828784359838267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814167267219189573225511 2721250900828784359838267)
          ·
            refine ⟨4081876351243176539757401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721250900828784359838267 4081876351243176539757401)
            ·
              refine ⟨3061407263432382404818051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081876351243176539757401 3061407263432382404818051)
              ·
                refine ⟨4592110895148573607227077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061407263432382404818051 4592110895148573607227077)
                ·
                  refine ⟨861020792840357551355077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4592110895148573607227077 861020792840357551355077)
                  ·
                    refine ⟨161441398657567040879077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861020792840357551355077 161441398657567040879077)
                    ·
                      rfl

theorem cell22_471609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_471609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471609 prefixEnd_471609 := by exact prefixLift 471609
  have htrace : WordTrace (prefixWord ++ tailWord_471609) baseStart_471609 baseEnd_471609 := by
    simpa [prefixWord, tailWord_471609, baseEnd_471609] using wordTrace_append hprefix tailTrace_471609
  have hstable : (prefixWord ++ tailWord_471609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471609).length < 2 ^ (prefixWord ++ tailWord_471609).sum := by decide
  have hdescent : baseEnd_471609 < baseStart_471609 := by decide
  rcases family_descends (prefixWord ++ tailWord_471609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471628 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_471628 : Nat := 118140960795 + 471628 * 2 ^ 59
def prefixEnd_471628 : Nat := 4983230072969 + 3 ^ 40 * 471628 * 2
def baseEnd_471628 : Nat := 161447902745857324654019

theorem tailTrace_471628 : CollatzResearch.WordTrace tailWord_471628 prefixEnd_471628 161447902745857324654019 := by
  unfold tailWord_471628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600843167689889247391769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11467790890253185663189025 8600843167689889247391769)
  ·
    refine ⟨6450632375767416935543827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8600843167689889247391769 6450632375767416935543827)
    ·
      refine ⟨9675948563651125403315741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450632375767416935543827 9675948563651125403315741)
      ·
        refine ⟨3628480711369172026243403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9675948563651125403315741 3628480711369172026243403)
        ·
          refine ⟨5442721067053758039365105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628480711369172026243403 5442721067053758039365105)
          ·
            refine ⟨4082040800290318529523829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442721067053758039365105 4082040800290318529523829)
            ·
              refine ⟨382691325027217362142859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4082040800290318529523829 382691325027217362142859)
              ·
                refine ⟨574036987540826043214289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382691325027217362142859 574036987540826043214289)
                ·
                  refine ⟨430527740655619532410717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574036987540826043214289 430527740655619532410717)
                  ·
                    refine ⟨161447902745857324654019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430527740655619532410717 161447902745857324654019)
                    ·
                      rfl

theorem cell22_471628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_471628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471628 prefixEnd_471628 := by exact prefixLift 471628
  have htrace : WordTrace (prefixWord ++ tailWord_471628) baseStart_471628 baseEnd_471628 := by
    simpa [prefixWord, tailWord_471628, baseEnd_471628] using wordTrace_append hprefix tailTrace_471628
  have hstable : (prefixWord ++ tailWord_471628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471628).length < 2 ^ (prefixWord ++ tailWord_471628).sum := by decide
  have hdescent : baseEnd_471628 < baseStart_471628 := by decide
  rcases family_descends (prefixWord ++ tailWord_471628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471673 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_471673 : Nat := 118140960795 + 471673 * 2 ^ 59
def prefixEnd_471673 : Nat := 4983230072969 + 3 ^ 40 * 471673 * 2
def baseEnd_471673 : Nat := 161463307165492207278881

theorem tailTrace_471673 : CollatzResearch.WordTrace tailWord_471673 prefixEnd_471673 161463307165492207278881 := by
  unfold tailWord_471673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203327620216751180171673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11468885080144500786781115 17203327620216751180171673)
  ·
    refine ⟨12902495715162563385128755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17203327620216751180171673 12902495715162563385128755)
    ·
      refine ⟨19353743572743845077693133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902495715162563385128755 19353743572743845077693133)
      ·
        refine ⟨7257653839778941904134925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19353743572743845077693133 7257653839778941904134925)
        ·
          refine ⟨2721620189917103214050597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7257653839778941904134925 2721620189917103214050597)
          ·
            refine ⟨510303785609456852634487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2721620189917103214050597 510303785609456852634487)
            ·
              refine ⟨765455678414185278951731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510303785609456852634487 765455678414185278951731)
              ·
                refine ⟨1148183517621277918427597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765455678414185278951731 1148183517621277918427597)
                ·
                  refine ⟨430568819107979219410349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148183517621277918427597 430568819107979219410349)
                  ·
                    refine ⟨161463307165492207278881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430568819107979219410349 161463307165492207278881)
                    ·
                      rfl

theorem cell22_471673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_471673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471673 prefixEnd_471673 := by exact prefixLift 471673
  have htrace : WordTrace (prefixWord ++ tailWord_471673) baseStart_471673 baseEnd_471673 := by
    simpa [prefixWord, tailWord_471673, baseEnd_471673] using wordTrace_append hprefix tailTrace_471673
  have hstable : (prefixWord ++ tailWord_471673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471673).length < 2 ^ (prefixWord ++ tailWord_471673).sum := by decide
  have hdescent : baseEnd_471673 < baseStart_471673 := by decide
  rcases family_descends (prefixWord ++ tailWord_471673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471699 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_471699 : Nat := 118140960795 + 471699 * 2 ^ 59
def prefixEnd_471699 : Nat := 4983230072969 + 3 ^ 40 * 471699 * 2
def baseEnd_471699 : Nat := 161472207496836806128801

theorem tailTrace_471699 : CollatzResearch.WordTrace tailWord_471699 prefixEnd_471699 161472207496836806128801 := by
  unfold tailWord_471699
  simp only [CollatzResearch.WordTrace]
  refine ⟨17204275918122557620618151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11469517278748371747078767 17204275918122557620618151)
  ·
    refine ⟨25806413877183836430927227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17204275918122557620618151 25806413877183836430927227)
    ·
      refine ⟨38709620815775754646390841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25806413877183836430927227 38709620815775754646390841)
      ·
        refine ⟨29032215611831815984793131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38709620815775754646390841 29032215611831815984793131)
        ·
          refine ⟨43548323417747723977189697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29032215611831815984793131 43548323417747723977189697)
          ·
            refine ⟨32661242563310792982892273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43548323417747723977189697 32661242563310792982892273)
            ·
              refine ⟨24495931922483094737169205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32661242563310792982892273 24495931922483094737169205)
              ·
                refine ⟨2296493617732790131609613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24495931922483094737169205 2296493617732790131609613)
                ·
                  refine ⟨861185106649796299353605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2296493617732790131609613 861185106649796299353605)
                  ·
                    refine ⟨161472207496836806128801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861185106649796299353605 161472207496836806128801)
                    ·
                      rfl

theorem cell22_471699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_471699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471699 prefixEnd_471699 := by exact prefixLift 471699
  have htrace : WordTrace (prefixWord ++ tailWord_471699) baseStart_471699 baseEnd_471699 := by
    simpa [prefixWord, tailWord_471699, baseEnd_471699] using wordTrace_append hprefix tailTrace_471699
  have hstable : (prefixWord ++ tailWord_471699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471699).length < 2 ^ (prefixWord ++ tailWord_471699).sum := by decide
  have hdescent : baseEnd_471699 < baseStart_471699 := by decide
  rcases family_descends (prefixWord ++ tailWord_471699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471780 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_471780 : Nat := 118140960795 + 471780 * 2 ^ 59
def prefixEnd_471780 : Nat := 4983230072969 + 3 ^ 40 * 471780 * 2
def baseEnd_471780 : Nat := 161499935452179594853553

theorem tailTrace_471780 : CollatzResearch.WordTrace tailWord_471780 prefixEnd_471780 161499935452179594853553 := by
  unfold tailWord_471780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603615115414554227158397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11471486820552738969544529 8603615115414554227158397)
  ·
    refine ⟨3226355668280457835184399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8603615115414554227158397 3226355668280457835184399)
    ·
      refine ⟨4839533502420686752776599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3226355668280457835184399 4839533502420686752776599)
      ·
        refine ⟨7259300253631030129164899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839533502420686752776599 7259300253631030129164899)
        ·
          refine ⟨10888950380446545193747349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259300253631030129164899 10888950380446545193747349)
          ·
            refine ⟨510419549083431805956907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10888950380446545193747349 510419549083431805956907)
            ·
              refine ⟨765629323625147708935361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510419549083431805956907 765629323625147708935361)
              ·
                refine ⟨574221992718860781701521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765629323625147708935361 574221992718860781701521)
                ·
                  refine ⟨430666494539145586276141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574221992718860781701521 430666494539145586276141)
                  ·
                    refine ⟨161499935452179594853553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430666494539145586276141 161499935452179594853553)
                    ·
                      rfl

theorem cell22_471780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_471780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471780 prefixEnd_471780 := by exact prefixLift 471780
  have htrace : WordTrace (prefixWord ++ tailWord_471780) baseStart_471780 baseEnd_471780 := by
    simpa [prefixWord, tailWord_471780, baseEnd_471780] using wordTrace_append hprefix tailTrace_471780
  have hstable : (prefixWord ++ tailWord_471780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471780).length < 2 ^ (prefixWord ++ tailWord_471780).sum := by decide
  have hdescent : baseEnd_471780 < baseStart_471780 := by decide
  rcases family_descends (prefixWord ++ tailWord_471780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471810 : List Nat := [3, 4, 1, 1, 1, 4, 2, 6]
def baseStart_471810 : Nat := 118140960795 + 471810 * 2 ^ 59
def prefixEnd_471810 : Nat := 4983230072969 + 3 ^ 40 * 471810 * 2
def baseEnd_471810 : Nat := 17945578340585501844829

theorem tailTrace_471810 : CollatzResearch.WordTrace tailWord_471810 prefixEnd_471810 17945578340585501844829 := by
  unfold tailWord_471810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302081105180105894477221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11472216280480282385272589 4302081105180105894477221)
  ·
    refine ⟨806640207221269855214479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4302081105180105894477221 806640207221269855214479)
    ·
      refine ⟨1209960310831904782821719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806640207221269855214479 1209960310831904782821719)
      ·
        refine ⟨1814940466247857174232579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209960310831904782821719 1814940466247857174232579)
        ·
          refine ⟨2722410699371785761348869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814940466247857174232579 2722410699371785761348869)
          ·
            refine ⟨510452006132209830252913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2722410699371785761348869 510452006132209830252913)
            ·
              refine ⟨382839004599157372689685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510452006132209830252913 382839004599157372689685)
              ·
                refine ⟨17945578340585501844829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 382839004599157372689685 17945578340585501844829)
                ·
                  rfl

theorem cell22_471810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_471810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471810 prefixEnd_471810 := by exact prefixLift 471810
  have htrace : WordTrace (prefixWord ++ tailWord_471810) baseStart_471810 baseEnd_471810 := by
    simpa [prefixWord, tailWord_471810, baseEnd_471810] using wordTrace_append hprefix tailTrace_471810
  have hstable : (prefixWord ++ tailWord_471810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471810).length < 2 ^ (prefixWord ++ tailWord_471810).sum := by decide
  have hdescent : baseEnd_471810 < baseStart_471810 := by decide
  rcases family_descends (prefixWord ++ tailWord_471810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471825 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_471825 : Nat := 118140960795 + 471825 * 2 ^ 59
def prefixEnd_471825 : Nat := 4983230072969 + 3 ^ 40 * 471825 * 2
def baseEnd_471825 : Nat := 161515339871814477478415

theorem tailTrace_471825 : CollatzResearch.WordTrace tailWord_471825 prefixEnd_471825 161515339871814477478415 := by
  unfold tailWord_471825
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208871515666081139704929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11472581010444054093136619 17208871515666081139704929)
  ·
    refine ⟨12906653636749560854778697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17208871515666081139704929 12906653636749560854778697)
    ·
      refine ⟨9679990227562170641084023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12906653636749560854778697 9679990227562170641084023)
      ·
        refine ⟨14519985341343255961626035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679990227562170641084023 14519985341343255961626035)
        ·
          refine ⟨21779978012014883942439053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519985341343255961626035 21779978012014883942439053)
          ·
            refine ⟨8167491754505581478414645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21779978012014883942439053 8167491754505581478414645)
            ·
              refine ⟨765702351984898263601373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8167491754505581478414645 765702351984898263601373)
              ·
                refine ⟨287138381994336848850515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765702351984898263601373 287138381994336848850515)
                ·
                  refine ⟨430707572991505273275773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287138381994336848850515 430707572991505273275773)
                  ·
                    refine ⟨161515339871814477478415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430707572991505273275773 161515339871814477478415)
                    ·
                      rfl

theorem cell22_471825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_471825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471825 prefixEnd_471825 := by exact prefixLift 471825
  have htrace : WordTrace (prefixWord ++ tailWord_471825) baseStart_471825 baseEnd_471825 := by
    simpa [prefixWord, tailWord_471825, baseEnd_471825] using wordTrace_append hprefix tailTrace_471825
  have hstable : (prefixWord ++ tailWord_471825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471825).length < 2 ^ (prefixWord ++ tailWord_471825).sum := by decide
  have hdescent : baseEnd_471825 < baseStart_471825 := by decide
  rcases family_descends (prefixWord ++ tailWord_471825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471881 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_471881 : Nat := 118140960795 + 471881 * 2 ^ 59
def prefixEnd_471881 : Nat := 4983230072969 + 3 ^ 40 * 471881 * 2
def baseEnd_471881 : Nat := 161534509816248998078243

theorem tailTrace_471881 : CollatzResearch.WordTrace tailWord_471881 prefixEnd_471881 161534509816248998078243 := by
  unfold tailWord_471881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17210914003463202703743497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11473942668975468469162331 17210914003463202703743497)
  ·
    refine ⟨12908185502597402027807623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17210914003463202703743497 12908185502597402027807623)
    ·
      refine ⟨19362278253896103041711435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12908185502597402027807623 19362278253896103041711435)
      ·
        refine ⟨29043417380844154562567153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19362278253896103041711435 29043417380844154562567153)
        ·
          refine ⟨21782563035633115921925365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29043417380844154562567153 21782563035633115921925365)
          ·
            refine ⟨2042115284590604617680503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21782563035633115921925365 2042115284590604617680503)
            ·
              refine ⟨3063172926885906926520755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042115284590604617680503 3063172926885906926520755)
              ·
                refine ⟨4594759390328860389781133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063172926885906926520755 4594759390328860389781133)
                ·
                  refine ⟨1723034771373322646167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594759390328860389781133 1723034771373322646167925)
                  ·
                    refine ⟨161534509816248998078243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1723034771373322646167925 161534509816248998078243)
                    ·
                      rfl

theorem cell22_471881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_471881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471881 prefixEnd_471881 := by exact prefixLift 471881
  have htrace : WordTrace (prefixWord ++ tailWord_471881) baseStart_471881 baseEnd_471881 := by
    simpa [prefixWord, tailWord_471881, baseEnd_471881] using wordTrace_append hprefix tailTrace_471881
  have hstable : (prefixWord ++ tailWord_471881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471881).length < 2 ^ (prefixWord ++ tailWord_471881).sum := by decide
  have hdescent : baseEnd_471881 < baseStart_471881 := by decide
  rcases family_descends (prefixWord ++ tailWord_471881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471934 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_471934 : Nat := 118140960795 + 471934 * 2 ^ 59
def prefixEnd_471934 : Nat := 4983230072969 + 3 ^ 40 * 471934 * 2
def baseEnd_471934 : Nat := 53850884266458175501027

theorem tailTrace_471934 : CollatzResearch.WordTrace tailWord_471934 prefixEnd_471934 53850884266458175501027 := by
  unfold tailWord_471934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151605884033899094427857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11475231381514128503615237 2151605884033899094427857)
  ·
    refine ⟨1613704413025424320820893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2151605884033899094427857 1613704413025424320820893)
    ·
      refine ⟨605139154884534120307835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1613704413025424320820893 605139154884534120307835)
      ·
        refine ⟨907708732326801180461753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605139154884534120307835 907708732326801180461753)
        ·
          refine ⟨680781549245100885346315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907708732326801180461753 680781549245100885346315)
          ·
            refine ⟨1021172323867651328019473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680781549245100885346315 1021172323867651328019473)
            ·
              refine ⟨765879242900738496014605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021172323867651328019473 765879242900738496014605)
              ·
                refine ⟨287204716087776936005477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765879242900738496014605 287204716087776936005477)
                ·
                  refine ⟨53850884266458175501027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287204716087776936005477 53850884266458175501027)
                  ·
                    rfl

theorem cell22_471934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_471934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_471934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_471934 prefixEnd_471934 := by exact prefixLift 471934
  have htrace : WordTrace (prefixWord ++ tailWord_471934) baseStart_471934 baseEnd_471934 := by
    simpa [prefixWord, tailWord_471934, baseEnd_471934] using wordTrace_append hprefix tailTrace_471934
  have hstable : (prefixWord ++ tailWord_471934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471934).length < 2 ^ (prefixWord ++ tailWord_471934).sum := by decide
  have hdescent : baseEnd_471934 < baseStart_471934 := by decide
  rcases family_descends (prefixWord ++ tailWord_471934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472033 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_472033 : Nat := 118140960795 + 472033 * 2 ^ 59
def prefixEnd_472033 : Nat := 4983230072969 + 3 ^ 40 * 472033 * 2
def baseEnd_472033 : Nat := 161586542522571268277777

theorem tailTrace_472033 : CollatzResearch.WordTrace tailWord_472033 prefixEnd_472033 161586542522571268277777 := by
  unfold tailWord_472033
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216457898912532663276753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11477638599275021775517835 17216457898912532663276753)
  ·
    refine ⟨12912343424184399497457565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17216457898912532663276753 12912343424184399497457565)
    ·
      refine ⟨4842128784069149811546587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12912343424184399497457565 4842128784069149811546587)
      ·
        refine ⟨7263193176103724717319881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4842128784069149811546587 7263193176103724717319881)
        ·
          refine ⟨5447394882077793537989911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263193176103724717319881 5447394882077793537989911)
          ·
            refine ⟨8171092323116690306984867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447394882077793537989911 8171092323116690306984867)
            ·
              refine ⟨12256638484675035460477301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171092323116690306984867 12256638484675035460477301)
              ·
                refine ⟨1149059857938284574419747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12256638484675035460477301 1149059857938284574419747)
                ·
                  refine ⟨1723589786907426861629621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149059857938284574419747 1723589786907426861629621)
                  ·
                    refine ⟨161586542522571268277777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1723589786907426861629621 161586542522571268277777)
                    ·
                      rfl

theorem cell22_472033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_472033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472033 prefixEnd_472033 := by exact prefixLift 472033
  have htrace : WordTrace (prefixWord ++ tailWord_472033) baseStart_472033 baseEnd_472033 := by
    simpa [prefixWord, tailWord_472033, baseEnd_472033] using wordTrace_append hprefix tailTrace_472033
  have hstable : (prefixWord ++ tailWord_472033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472033).length < 2 ^ (prefixWord ++ tailWord_472033).sum := by decide
  have hdescent : baseEnd_472033 < baseStart_472033 := by decide
  rcases family_descends (prefixWord ++ tailWord_472033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472037 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_472037 : Nat := 118140960795 + 472037 * 2 ^ 59
def prefixEnd_472037 : Nat := 4983230072969 + 3 ^ 40 * 472037 * 2
def baseEnd_472037 : Nat := 161587911804316591177765

theorem tailTrace_472037 : CollatzResearch.WordTrace tailWord_472037 prefixEnd_472037 161587911804316591177765 := by
  unfold tailWord_472037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216603790898041346422365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11477735860598694230948243 17216603790898041346422365)
  ·
    refine ⟨6456226421586765504908387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17216603790898041346422365 6456226421586765504908387)
    ·
      refine ⟨9684339632380148257362581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6456226421586765504908387 9684339632380148257362581)
      ·
        refine ⟨453953420267819449563871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9684339632380148257362581 453953420267819449563871)
        ·
          refine ⟨680930130401729174345807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453953420267819449563871 680930130401729174345807)
          ·
            refine ⟨1021395195602593761518711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680930130401729174345807 1021395195602593761518711)
            ·
              refine ⟨1532092793403890642278067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021395195602593761518711 1532092793403890642278067)
              ·
                refine ⟨2298139190105835963417101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532092793403890642278067 2298139190105835963417101)
                ·
                  refine ⟨861802196289688486281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2298139190105835963417101 861802196289688486281413)
                  ·
                    refine ⟨161587911804316591177765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861802196289688486281413 161587911804316591177765)
                    ·
                      rfl

theorem cell22_472037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_472037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472037 prefixEnd_472037 := by exact prefixLift 472037
  have htrace : WordTrace (prefixWord ++ tailWord_472037) baseStart_472037 baseEnd_472037 := by
    simpa [prefixWord, tailWord_472037, baseEnd_472037] using wordTrace_append hprefix tailTrace_472037
  have hstable : (prefixWord ++ tailWord_472037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472037).length < 2 ^ (prefixWord ++ tailWord_472037).sum := by decide
  have hdescent : baseEnd_472037 < baseStart_472037 := by decide
  rcases family_descends (prefixWord ++ tailWord_472037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472054 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_472054 : Nat := 118140960795 + 472054 * 2 ^ 59
def prefixEnd_472054 : Nat := 4983230072969 + 3 ^ 40 * 472054 * 2
def baseEnd_472054 : Nat := 161593731251734213502713

theorem tailTrace_472054 : CollatzResearch.WordTrace tailWord_472054 prefixEnd_472054 161593731251734213502713 := by
  unfold tailWord_472054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076076489489778328111951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11478149221224302166527477 1076076489489778328111951)
  ·
    refine ⟨1614114734234667492167927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076076489489778328111951 1614114734234667492167927)
    ·
      refine ⟨2421172101352001238251891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614114734234667492167927 2421172101352001238251891)
      ·
        refine ⟨3631758152028001857377837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421172101352001238251891 3631758152028001857377837)
        ·
          refine ⟨1361909307010500696516689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3631758152028001857377837 1361909307010500696516689)
          ·
            refine ⟨1021431980257875522387517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361909307010500696516689 1021431980257875522387517)
            ·
              refine ⟨383036992596703320895319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021431980257875522387517 383036992596703320895319)
              ·
                refine ⟨574555488895054981342979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383036992596703320895319 574555488895054981342979)
                ·
                  refine ⟨861833233342582472014469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574555488895054981342979 861833233342582472014469)
                  ·
                    refine ⟨161593731251734213502713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861833233342582472014469 161593731251734213502713)
                    ·
                      rfl

theorem cell22_472054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_472054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472054 prefixEnd_472054 := by exact prefixLift 472054
  have htrace : WordTrace (prefixWord ++ tailWord_472054) baseStart_472054 baseEnd_472054 := by
    simpa [prefixWord, tailWord_472054, baseEnd_472054] using wordTrace_append hprefix tailTrace_472054
  have hstable : (prefixWord ++ tailWord_472054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472054).length < 2 ^ (prefixWord ++ tailWord_472054).sum := by decide
  have hdescent : baseEnd_472054 < baseStart_472054 := by decide
  rcases family_descends (prefixWord ++ tailWord_472054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472065 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_472065 : Nat := 118140960795 + 472065 * 2 ^ 59
def prefixEnd_472065 : Nat := 4983230072969 + 3 ^ 40 * 472065 * 2
def baseEnd_472065 : Nat := 161597496776533851477679

theorem tailTrace_472065 : CollatzResearch.WordTrace tailWord_472065 prefixEnd_472065 161597496776533851477679 := by
  unfold tailWord_472065
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217625034796602128441649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11478416689864401418961099 17217625034796602128441649)
  ·
    refine ⟨12913218776097451596331237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17217625034796602128441649 12913218776097451596331237)
    ·
      refine ⟨2421228520518272174312107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12913218776097451596331237 2421228520518272174312107)
      ·
        refine ⟨3631842780777408261468161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421228520518272174312107 3631842780777408261468161)
        ·
          refine ⟨2723882085583056196101121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631842780777408261468161 2723882085583056196101121)
          ·
            refine ⟨2042911564187292147075841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723882085583056196101121 2042911564187292147075841)
            ·
              refine ⟨1532183673140469110306881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042911564187292147075841 1532183673140469110306881)
              ·
                refine ⟨1149137754855351832730161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532183673140469110306881 1149137754855351832730161)
                ·
                  refine ⟨861853316141513874547621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149137754855351832730161 861853316141513874547621)
                  ·
                    refine ⟨161597496776533851477679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 861853316141513874547621 161597496776533851477679)
                    ·
                      rfl

theorem cell22_472065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_472065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472065 prefixEnd_472065 := by exact prefixLift 472065
  have htrace : WordTrace (prefixWord ++ tailWord_472065) baseStart_472065 baseEnd_472065 := by
    simpa [prefixWord, tailWord_472065, baseEnd_472065] using wordTrace_append hprefix tailTrace_472065
  have hstable : (prefixWord ++ tailWord_472065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472065).length < 2 ^ (prefixWord ++ tailWord_472065).sum := by decide
  have hdescent : baseEnd_472065 < baseStart_472065 := by decide
  rcases family_descends (prefixWord ++ tailWord_472065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472095 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 5, 3]
def baseStart_472095 : Nat := 118140960795 + 472095 * 2 ^ 59
def prefixEnd_472095 : Nat := 4983230072969 + 3 ^ 40 * 472095 * 2
def baseEnd_472095 : Nat := 161607766389623773227587

theorem tailTrace_472095 : CollatzResearch.WordTrace tailWord_472095 prefixEnd_472095 161607766389623773227587 := by
  unfold tailWord_472095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218719224687917252033739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479146149791944834689159 17218719224687917252033739)
  ·
    refine ⟨25828078837031875878050609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218719224687917252033739 25828078837031875878050609)
    ·
      refine ⟨19371059127773906908537957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25828078837031875878050609 19371059127773906908537957)
      ·
        refine ⟨3632073586457607545350867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19371059127773906908537957 3632073586457607545350867)
        ·
          refine ⟨5448110379686411318026301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632073586457607545350867 5448110379686411318026301)
          ·
            refine ⟨2043041392382404244259863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5448110379686411318026301 2043041392382404244259863)
            ·
              refine ⟨3064562088573606366389795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043041392382404244259863 3064562088573606366389795)
              ·
                refine ⟨4596843132860409549584693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064562088573606366389795 4596843132860409549584693)
                ·
                  refine ⟨430954043705663395273565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4596843132860409549584693 430954043705663395273565)
                  ·
                    refine ⟨161607766389623773227587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430954043705663395273565 161607766389623773227587)
                    ·
                      rfl

theorem cell22_472095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_472095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472095 prefixEnd_472095 := by exact prefixLift 472095
  have htrace : WordTrace (prefixWord ++ tailWord_472095) baseStart_472095 baseEnd_472095 := by
    simpa [prefixWord, tailWord_472095, baseEnd_472095] using wordTrace_append hprefix tailTrace_472095
  have hstable : (prefixWord ++ tailWord_472095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472095).length < 2 ^ (prefixWord ++ tailWord_472095).sum := by decide
  have hdescent : baseEnd_472095 < baseStart_472095 := by decide
  rcases family_descends (prefixWord ++ tailWord_472095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472108 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_472108 : Nat := 118140960795 + 472108 * 2 ^ 59
def prefixEnd_472108 : Nat := 4983230072969 + 3 ^ 40 * 472108 * 2
def baseEnd_472108 : Nat := 53870738851765357550849

theorem tailTrace_472108 : CollatzResearch.WordTrace tailWord_472108 prefixEnd_472108 53870738851765357550849 := by
  unfold tailWord_472108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609596686820410236128489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11479462249093880314837985 8609596686820410236128489)
  ·
    refine ⟨6457197515115307677096367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8609596686820410236128489 6457197515115307677096367)
    ·
      refine ⟨9685796272672961515644551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457197515115307677096367 9685796272672961515644551)
      ·
        refine ⟨14528694409009442273466827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685796272672961515644551 14528694409009442273466827)
        ·
          refine ⟨21793041613514163410200241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528694409009442273466827 21793041613514163410200241)
          ·
            refine ⟨16344781210135622557650181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21793041613514163410200241 16344781210135622557650181)
            ·
              refine ⟨3064646476900429229559409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16344781210135622557650181 3064646476900429229559409)
              ·
                refine ⟨2298484857675321922169557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064646476900429229559409 2298484857675321922169557)
                ·
                  refine ⟨53870738851765357550849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2298484857675321922169557 53870738851765357550849)
                  ·
                    rfl

theorem cell22_472108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_472108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472108 prefixEnd_472108 := by exact prefixLift 472108
  have htrace : WordTrace (prefixWord ++ tailWord_472108) baseStart_472108 baseEnd_472108 := by
    simpa [prefixWord, tailWord_472108, baseEnd_472108] using wordTrace_append hprefix tailTrace_472108
  have hstable : (prefixWord ++ tailWord_472108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472108).length < 2 ^ (prefixWord ++ tailWord_472108).sum := by decide
  have hdescent : baseEnd_472108 < baseStart_472108 := by decide
  rcases family_descends (prefixWord ++ tailWord_472108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472125 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 7]
def baseStart_472125 : Nat := 118140960795 + 472125 * 2 ^ 59
def prefixEnd_472125 : Nat := 4983230072969 + 3 ^ 40 * 472125 * 2
def baseEnd_472125 : Nat := 53872678667571231659165

theorem tailTrace_472125 : CollatzResearch.WordTrace tailWord_472125 prefixEnd_472125 53872678667571231659165 := by
  unfold tailWord_472125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219813414579232375625829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479875609719488250417219 17219813414579232375625829)
  ·
    refine ⟨3228715015233606070429843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17219813414579232375625829 3228715015233606070429843)
    ·
      refine ⟨4843072522850409105644765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3228715015233606070429843 4843072522850409105644765)
      ·
        refine ⟨1816152196068903414616787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4843072522850409105644765 1816152196068903414616787)
        ·
          refine ⟨2724228294103355121925181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816152196068903414616787 2724228294103355121925181)
          ·
            refine ⟨1021585610288758170721943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2724228294103355121925181 1021585610288758170721943)
            ·
              refine ⟨1532378415433137256082915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021585610288758170721943 1532378415433137256082915)
              ·
                refine ⟨2298567623149705884124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532378415433137256082915 2298567623149705884124373)
                ·
                  refine ⟨53872678667571231659165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2298567623149705884124373 53872678667571231659165)
                  ·
                    rfl

theorem cell22_472125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_472125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472125 prefixEnd_472125 := by exact prefixLift 472125
  have htrace : WordTrace (prefixWord ++ tailWord_472125) baseStart_472125 baseEnd_472125 := by
    simpa [prefixWord, tailWord_472125, baseEnd_472125] using wordTrace_append hprefix tailTrace_472125
  have hstable : (prefixWord ++ tailWord_472125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472125).length < 2 ^ (prefixWord ++ tailWord_472125).sum := by decide
  have hdescent : baseEnd_472125 < baseStart_472125 := by decide
  rcases family_descends (prefixWord ++ tailWord_472125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472129 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_472129 : Nat := 118140960795 + 472129 * 2 ^ 59
def prefixEnd_472129 : Nat := 4983230072969 + 3 ^ 40 * 472129 * 2
def baseEnd_472129 : Nat := 161619405284459017877483

theorem tailTrace_472129 : CollatzResearch.WordTrace tailWord_472129 prefixEnd_472129 161619405284459017877483 := by
  unfold tailWord_472129
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219959306564741058771441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479972871043160705847627 17219959306564741058771441)
  ·
    refine ⟨12914969479923555794078581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17219959306564741058771441 12914969479923555794078581)
    ·
      refine ⟨1210778388742833355694867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12914969479923555794078581 1210778388742833355694867)
      ·
        refine ⟨1816167583114250033542301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210778388742833355694867 1816167583114250033542301)
        ·
          refine ⟨681062843667843762578363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1816167583114250033542301 681062843667843762578363)
          ·
            refine ⟨1021594265501765643867545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681062843667843762578363 1021594265501765643867545)
            ·
              refine ⟨766195699126324232900659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021594265501765643867545 766195699126324232900659)
              ·
                refine ⟨1149293548689486349350989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766195699126324232900659 1149293548689486349350989)
                ·
                  refine ⟨430985080758557381006621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149293548689486349350989 430985080758557381006621)
                  ·
                    refine ⟨161619405284459017877483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430985080758557381006621 161619405284459017877483)
                    ·
                      rfl

theorem cell22_472129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_472129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472129 prefixEnd_472129 := by exact prefixLift 472129
  have htrace : WordTrace (prefixWord ++ tailWord_472129) baseStart_472129 baseEnd_472129 := by
    simpa [prefixWord, tailWord_472129, baseEnd_472129] using wordTrace_append hprefix tailTrace_472129
  have hstable : (prefixWord ++ tailWord_472129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472129).length < 2 ^ (prefixWord ++ tailWord_472129).sum := by decide
  have hdescent : baseEnd_472129 < baseStart_472129 := by decide
  rcases family_descends (prefixWord ++ tailWord_472129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472142 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_472142 : Nat := 118140960795 + 472142 * 2 ^ 59
def prefixEnd_472142 : Nat := 4983230072969 + 3 ^ 40 * 472142 * 2
def baseEnd_472142 : Nat := 53874618483377105767481

theorem tailTrace_472142 : CollatzResearch.WordTrace tailWord_472142 prefixEnd_472142 53874618483377105767481 := by
  unfold tailWord_472142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152554181939705534874335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11480288970345096185996453 2152554181939705534874335)
  ·
    refine ⟨3228831272909558302311503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152554181939705534874335 3228831272909558302311503)
    ·
      refine ⟨4843246909364337453467255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3228831272909558302311503 4843246909364337453467255)
      ·
        refine ⟨7264870364046506180200883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843246909364337453467255 7264870364046506180200883)
        ·
          refine ⟨10897305546069759270301325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264870364046506180200883 10897305546069759270301325)
          ·
            refine ⟨4086489579776159726362997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10897305546069759270301325 4086489579776159726362997)
            ·
              refine ⟨383108398104014974346531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4086489579776159726362997 383108398104014974346531)
              ·
                refine ⟨574662597156022461519797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383108398104014974346531 574662597156022461519797)
                ·
                  refine ⟨53874618483377105767481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574662597156022461519797 53874618483377105767481)
                  ·
                    rfl

theorem cell22_472142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_472142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472142 prefixEnd_472142 := by exact prefixLift 472142
  have htrace : WordTrace (prefixWord ++ tailWord_472142) baseStart_472142 baseEnd_472142 := by
    simpa [prefixWord, tailWord_472142, baseEnd_472142] using wordTrace_append hprefix tailTrace_472142
  have hstable : (prefixWord ++ tailWord_472142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472142).length < 2 ^ (prefixWord ++ tailWord_472142).sum := by decide
  have hdescent : baseEnd_472142 < baseStart_472142 := by decide
  rcases family_descends (prefixWord ++ tailWord_472142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472153 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 8]
def baseStart_472153 : Nat := 118140960795 + 472153 * 2 ^ 59
def prefixEnd_472153 : Nat := 4983230072969 + 3 ^ 40 * 472153 * 2
def baseEnd_472153 : Nat := 53875873658310318425803

theorem tailTrace_472153 : CollatzResearch.WordTrace tailWord_472153 prefixEnd_472153 53875873658310318425803 := by
  unfold tailWord_472153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220834658477793157645113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11480556438985195438430075 17220834658477793157645113)
  ·
    refine ⟨12915625993858344868233835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17220834658477793157645113 12915625993858344868233835)
    ·
      refine ⟨19373438990787517302350753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915625993858344868233835 19373438990787517302350753)
      ·
        refine ⟨14530079243090637976763065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19373438990787517302350753 14530079243090637976763065)
        ·
          refine ⟨10897559432317978482572299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14530079243090637976763065 10897559432317978482572299)
          ·
            refine ⟨16346339148476967723858449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897559432317978482572299 16346339148476967723858449)
            ·
              refine ⟨12259754361357725792893837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16346339148476967723858449 12259754361357725792893837)
              ·
                refine ⟨4597407885509147172335189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12259754361357725792893837 4597407885509147172335189)
                ·
                  refine ⟨53875873658310318425803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4597407885509147172335189 53875873658310318425803)
                  ·
                    rfl

theorem cell22_472153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_472153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472153 prefixEnd_472153 := by exact prefixLift 472153
  have htrace : WordTrace (prefixWord ++ tailWord_472153) baseStart_472153 baseEnd_472153 := by
    simpa [prefixWord, tailWord_472153, baseEnd_472153] using wordTrace_append hprefix tailTrace_472153
  have hstable : (prefixWord ++ tailWord_472153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472153).length < 2 ^ (prefixWord ++ tailWord_472153).sum := by decide
  have hdescent : baseEnd_472153 < baseStart_472153 := by decide
  rcases family_descends (prefixWord ++ tailWord_472153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472215 : List Nat := [1, 1, 3, 3, 3, 1, 2, 8]
def baseStart_472215 : Nat := 118140960795 + 472215 * 2 ^ 59
def prefixEnd_472215 : Nat := 4983230072969 + 3 ^ 40 * 472215 * 2
def baseEnd_472215 : Nat := 17960982760220384469691

theorem tailTrace_472215 : CollatzResearch.WordTrace tailWord_472215 prefixEnd_472215 17960982760220384469691 := by
  unfold tailWord_472215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223095984253177746402099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11482063989502118497601399 17223095984253177746402099)
  ·
    refine ⟨25834643976379766619603149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17223095984253177746402099 25834643976379766619603149)
    ·
      refine ⟨9687991491142412482351181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25834643976379766619603149 9687991491142412482351181)
      ·
        refine ⟨3632996809178404680881693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9687991491142412482351181 3632996809178404680881693)
        ·
          refine ⟨1362373803441901755330635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3632996809178404680881693 1362373803441901755330635)
          ·
            refine ⟨2043560705162852632995953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362373803441901755330635 2043560705162852632995953)
            ·
              refine ⟨1532670528872139474746965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043560705162852632995953 1532670528872139474746965)
              ·
                refine ⟨17960982760220384469691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1532670528872139474746965 17960982760220384469691)
                ·
                  rfl

theorem cell22_472215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 8].length) (baseStart_472215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472215 prefixEnd_472215 := by exact prefixLift 472215
  have htrace : WordTrace (prefixWord ++ tailWord_472215) baseStart_472215 baseEnd_472215 := by
    simpa [prefixWord, tailWord_472215, baseEnd_472215] using wordTrace_append hprefix tailTrace_472215
  have hstable : (prefixWord ++ tailWord_472215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472215).length < 2 ^ (prefixWord ++ tailWord_472215).sum := by decide
  have hdescent : baseEnd_472215 < baseStart_472215 := by decide
  rcases family_descends (prefixWord ++ tailWord_472215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472234 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_472234 : Nat := 118140960795 + 472234 * 2 ^ 59
def prefixEnd_472234 : Nat := 4983230072969 + 3 ^ 40 * 472234 * 2
def baseEnd_472234 : Nat := 161655348930273744002161

theorem tailTrace_472234 : CollatzResearch.WordTrace tailWord_472234 prefixEnd_472234 161655348930273744002161 := by
  unfold tailWord_472234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305947242796085997835939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11482525980789562660895837 4305947242796085997835939)
  ·
    refine ⟨6458920864194128996753909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4305947242796085997835939 6458920864194128996753909)
    ·
      refine ⟨605523831018199593445679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6458920864194128996753909 605523831018199593445679)
      ·
        refine ⟨908285746527299390168519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605523831018199593445679 908285746527299390168519)
        ·
          refine ⟨1362428619790949085252779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908285746527299390168519 1362428619790949085252779)
          ·
            refine ⟨2043642929686423627879169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362428619790949085252779 2043642929686423627879169)
            ·
              refine ⟨1532732197264817720909377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043642929686423627879169 1532732197264817720909377)
              ·
                refine ⟨1149549147948613290682033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532732197264817720909377 1149549147948613290682033)
                ·
                  refine ⟨862161860961459968011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149549147948613290682033 862161860961459968011525)
                  ·
                    refine ⟨161655348930273744002161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862161860961459968011525 161655348930273744002161)
                    ·
                      rfl

theorem cell22_472234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_472234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472234 prefixEnd_472234 := by exact prefixLift 472234
  have htrace : WordTrace (prefixWord ++ tailWord_472234) baseStart_472234 baseEnd_472234 := by
    simpa [prefixWord, tailWord_472234, baseEnd_472234] using wordTrace_append hprefix tailTrace_472234
  have hstable : (prefixWord ++ tailWord_472234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472234).length < 2 ^ (prefixWord ++ tailWord_472234).sum := by decide
  have hdescent : baseEnd_472234 < baseStart_472234 := by decide
  rcases family_descends (prefixWord ++ tailWord_472234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472247 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 3, 3]
def baseStart_472247 : Nat := 118140960795 + 472247 * 2 ^ 59
def prefixEnd_472247 : Nat := 4983230072969 + 3 ^ 40 * 472247 * 2
def baseEnd_472247 : Nat := 161659799095946043427121

theorem tailTrace_472247 : CollatzResearch.WordTrace tailWord_472247 prefixEnd_472247 161659799095946043427121 := by
  unfold tailWord_472247
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224263120137247211566995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11482842080091498141044663 17224263120137247211566995)
  ·
    refine ⟨25836394680205870817350493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17224263120137247211566995 25836394680205870817350493)
    ·
      refine ⟨9688648005077201556506435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25836394680205870817350493 9688648005077201556506435)
      ·
        refine ⟨14532972007615802334759653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688648005077201556506435 14532972007615802334759653)
        ·
          refine ⟨2724932251427962937767435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14532972007615802334759653 2724932251427962937767435)
          ·
            refine ⟨4087398377141944406651153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724932251427962937767435 4087398377141944406651153)
            ·
              refine ⟨3065548782856458304988365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087398377141944406651153 3065548782856458304988365)
              ·
                refine ⟨1149580793571171864370637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3065548782856458304988365 1149580793571171864370637)
                ·
                  refine ⟨431092797589189449138989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149580793571171864370637 431092797589189449138989)
                  ·
                    refine ⟨161659799095946043427121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431092797589189449138989 161659799095946043427121)
                    ·
                      rfl

theorem cell22_472247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_472247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472247 prefixEnd_472247 := by exact prefixLift 472247
  have htrace : WordTrace (prefixWord ++ tailWord_472247) baseStart_472247 baseEnd_472247 := by
    simpa [prefixWord, tailWord_472247, baseEnd_472247] using wordTrace_append hprefix tailTrace_472247
  have hstable : (prefixWord ++ tailWord_472247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472247).length < 2 ^ (prefixWord ++ tailWord_472247).sum := by decide
  have hdescent : baseEnd_472247 < baseStart_472247 := by decide
  rcases family_descends (prefixWord ++ tailWord_472247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472324 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_472324 : Nat := 118140960795 + 472324 * 2 ^ 59
def prefixEnd_472324 : Nat := 4983230072969 + 3 ^ 40 * 472324 * 2
def baseEnd_472324 : Nat := 161686157769543509251885

theorem tailTrace_472324 : CollatzResearch.WordTrace tailWord_472324 prefixEnd_472324 161686157769543509251885 := by
  unfold tailWord_472324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613535770429144681060013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11484714360572192908080017 8613535770429144681060013)
  ·
    refine ⟨3230075913910929255397505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8613535770429144681060013 3230075913910929255397505)
    ·
      refine ⟨2422556935433196941548129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3230075913910929255397505 2422556935433196941548129)
      ·
        refine ⟨1816917701574897706161097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2422556935433196941548129 1816917701574897706161097)
        ·
          refine ⟨1362688276181173279620823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816917701574897706161097 1362688276181173279620823)
          ·
            refine ⟨2044032414271759919431235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362688276181173279620823 2044032414271759919431235)
            ·
              refine ⟨3066048621407639879146853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044032414271759919431235 3066048621407639879146853)
              ·
                refine ⟨574884116513932477340035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3066048621407639879146853 574884116513932477340035)
                ·
                  refine ⟨862326174770898716010053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574884116513932477340035 862326174770898716010053)
                  ·
                    refine ⟨161686157769543509251885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862326174770898716010053 161686157769543509251885)
                    ·
                      rfl

theorem cell22_472324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_472324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472324 prefixEnd_472324 := by exact prefixLift 472324
  have htrace : WordTrace (prefixWord ++ tailWord_472324) baseStart_472324 baseEnd_472324 := by
    simpa [prefixWord, tailWord_472324, baseEnd_472324] using wordTrace_append hprefix tailTrace_472324
  have hstable : (prefixWord ++ tailWord_472324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472324).length < 2 ^ (prefixWord ++ tailWord_472324).sum := by decide
  have hdescent : baseEnd_472324 < baseStart_472324 := by decide
  rcases family_descends (prefixWord ++ tailWord_472324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472337 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_472337 : Nat := 118140960795 + 472337 * 2 ^ 59
def prefixEnd_472337 : Nat := 4983230072969 + 3 ^ 40 * 472337 * 2
def baseEnd_472337 : Nat := 161690607935215808676845

theorem tailTrace_472337 : CollatzResearch.WordTrace tailWord_472337 prefixEnd_472337 161690607935215808676845 := by
  unfold tailWord_472337
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227545689811192582343265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485030459874128388228843 17227545689811192582343265)
  ·
    refine ⟨12920659267358394436757449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17227545689811192582343265 12920659267358394436757449)
    ·
      refine ⟨9690494450518795827568087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12920659267358394436757449 9690494450518795827568087)
      ·
        refine ⟨14535741675778193741352131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690494450518795827568087 14535741675778193741352131)
        ·
          refine ⟨21803612513667290612028197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14535741675778193741352131 21803612513667290612028197)
          ·
            refine ⟨4088177346312616989755287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21803612513667290612028197 4088177346312616989755287)
            ·
              refine ⟨6132266019468925484632931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088177346312616989755287 6132266019468925484632931)
              ·
                refine ⟨9198399029203388226949397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132266019468925484632931 9198399029203388226949397)
                ·
                  refine ⟨431174954493908823138253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9198399029203388226949397 431174954493908823138253)
                  ·
                    refine ⟨161690607935215808676845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431174954493908823138253 161690607935215808676845)
                    ·
                      rfl

theorem cell22_472337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_472337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472337 prefixEnd_472337 := by exact prefixLift 472337
  have htrace : WordTrace (prefixWord ++ tailWord_472337) baseStart_472337 baseEnd_472337 := by
    simpa [prefixWord, tailWord_472337, baseEnd_472337] using wordTrace_append hprefix tailTrace_472337
  have hstable : (prefixWord ++ tailWord_472337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472337).length < 2 ^ (prefixWord ++ tailWord_472337).sum := by decide
  have hdescent : baseEnd_472337 < baseStart_472337 := by decide
  rcases family_descends (prefixWord ++ tailWord_472337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472356 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_472356 : Nat := 118140960795 + 472356 * 2 ^ 59
def prefixEnd_472356 : Nat := 4983230072969 + 3 ^ 40 * 472356 * 2
def baseEnd_472356 : Nat := 53899037341168697483929

theorem tailTrace_472356 : CollatzResearch.WordTrace tailWord_472356 prefixEnd_472356 53899037341168697483929 := by
  unfold tailWord_472356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614119338371179413642461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11485492451161572551523281 8614119338371179413642461)
  ·
    refine ⟨3230294751889192280115923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8614119338371179413642461 3230294751889192280115923)
    ·
      refine ⟨4845442127833788420173885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230294751889192280115923 4845442127833788420173885)
      ·
        refine ⟨1817040797937670657565207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4845442127833788420173885 1817040797937670657565207)
        ·
          refine ⟨2725561196906505986347811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817040797937670657565207 2725561196906505986347811)
          ·
            refine ⟨4088341795359758979521717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725561196906505986347811 4088341795359758979521717)
            ·
              refine ⟨383282043314977404330161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4088341795359758979521717 383282043314977404330161)
              ·
                refine ⟨287461532486233053247621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383282043314977404330161 287461532486233053247621)
                ·
                  refine ⟨53899037341168697483929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287461532486233053247621 53899037341168697483929)
                  ·
                    rfl

theorem cell22_472356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_472356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472356 prefixEnd_472356 := by exact prefixLift 472356
  have htrace : WordTrace (prefixWord ++ tailWord_472356) baseStart_472356 baseEnd_472356 := by
    simpa [prefixWord, tailWord_472356, baseEnd_472356] using wordTrace_append hprefix tailTrace_472356
  have hstable : (prefixWord ++ tailWord_472356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472356).length < 2 ^ (prefixWord ++ tailWord_472356).sum := by decide
  have hdescent : baseEnd_472356 < baseStart_472356 := by decide
  rcases family_descends (prefixWord ++ tailWord_472356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472371 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 2, 3]
def baseStart_472371 : Nat := 118140960795 + 472371 * 2 ^ 59
def prefixEnd_472371 : Nat := 4983230072969 + 3 ^ 40 * 472371 * 2
def baseEnd_472371 : Nat := 161702246830051053326741

theorem tailTrace_472371 : CollatzResearch.WordTrace tailWord_472371 prefixEnd_472371 161702246830051053326741 := by
  unfold tailWord_472371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228785771688016389080967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485857181125344259387311 17228785771688016389080967)
  ·
    refine ⟨25843178657532024583621451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17228785771688016389080967 25843178657532024583621451)
    ·
      refine ⟨38764767986298036875432177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25843178657532024583621451 38764767986298036875432177)
      ·
        refine ⟨29073575989723527656574133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38764767986298036875432177 29073575989723527656574133)
        ·
          refine ⟨2725647749036580717803825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29073575989723527656574133 2725647749036580717803825)
          ·
            refine ⟨2044235811777435538352869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725647749036580717803825 2044235811777435538352869)
            ·
              refine ⟨383294214708269163441163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2044235811777435538352869 383294214708269163441163)
              ·
                refine ⟨574941322062403745161745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383294214708269163441163 574941322062403745161745)
                ·
                  refine ⟨431205991546802808871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574941322062403745161745 431205991546802808871309)
                  ·
                    refine ⟨161702246830051053326741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431205991546802808871309 161702246830051053326741)
                    ·
                      rfl

theorem cell22_472371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 3].length) (baseStart_472371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472371 prefixEnd_472371 := by exact prefixLift 472371
  have htrace : WordTrace (prefixWord ++ tailWord_472371) baseStart_472371 baseEnd_472371 := by
    simpa [prefixWord, tailWord_472371, baseEnd_472371] using wordTrace_append hprefix tailTrace_472371
  have hstable : (prefixWord ++ tailWord_472371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472371).length < 2 ^ (prefixWord ++ tailWord_472371).sum := by decide
  have hdescent : baseEnd_472371 < baseStart_472371 := by decide
  rcases family_descends (prefixWord ++ tailWord_472371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472429 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 5]
def baseStart_472429 : Nat := 118140960795 + 472429 * 2 ^ 59
def prefixEnd_472429 : Nat := 4983230072969 + 3 ^ 40 * 472429 * 2
def baseEnd_472429 : Nat := 53907367138452745125521

theorem tailTrace_472429 : CollatzResearch.WordTrace tailWord_472429 prefixEnd_472429 53907367138452745125521 := by
  unfold tailWord_472429
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230901205477892294692341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11487267470318594863128227 17230901205477892294692341)
  ·
    refine ⟨1615396988013552402627407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17230901205477892294692341 1615396988013552402627407)
    ·
      refine ⟨2423095482020328603941111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615396988013552402627407 2423095482020328603941111)
      ·
        refine ⟨3634643223030492905911667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423095482020328603941111 3634643223030492905911667)
        ·
          refine ⟨5451964834545739358867501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634643223030492905911667 5451964834545739358867501)
          ·
            refine ⟨2044486812954652259575313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5451964834545739358867501 2044486812954652259575313)
            ·
              refine ⟨1533365109715989194681485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044486812954652259575313 1533365109715989194681485)
              ·
                refine ⟨575011916143495948005557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1533365109715989194681485 575011916143495948005557)
                ·
                  refine ⟨53907367138452745125521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575011916143495948005557 53907367138452745125521)
                  ·
                    rfl

theorem cell22_472429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_472429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472429 prefixEnd_472429 := by exact prefixLift 472429
  have htrace : WordTrace (prefixWord ++ tailWord_472429) baseStart_472429 baseEnd_472429 := by
    simpa [prefixWord, tailWord_472429, baseEnd_472429] using wordTrace_append hprefix tailTrace_472429
  have hstable : (prefixWord ++ tailWord_472429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472429).length < 2 ^ (prefixWord ++ tailWord_472429).sum := by decide
  have hdescent : baseEnd_472429 < baseStart_472429 := by decide
  rcases family_descends (prefixWord ++ tailWord_472429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472450 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_472450 : Nat := 118140960795 + 472450 * 2 ^ 59
def prefixEnd_472450 : Nat := 4983230072969 + 3 ^ 40 * 472450 * 2
def baseEnd_472450 : Nat := 161729290144521180601499

theorem tailTrace_472450 : CollatzResearch.WordTrace tailWord_472450 prefixEnd_472450 161729290144521180601499 := by
  unfold tailWord_472450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307916784600453220301701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11487778092267875254137869 4307916784600453220301701)
  ·
    refine ⟨807734397112584978806569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4307916784600453220301701 807734397112584978806569)
    ·
      refine ⟨605800797834438734104927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807734397112584978806569 605800797834438734104927)
      ·
        refine ⟨908701196751658101157391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605800797834438734104927 908701196751658101157391)
        ·
          refine ⟨1363051795127487151736087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908701196751658101157391 1363051795127487151736087)
          ·
            refine ⟨2044577692691230727604131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363051795127487151736087 2044577692691230727604131)
            ·
              refine ⟨3066866539036846091406197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044577692691230727604131 3066866539036846091406197)
              ·
                refine ⟨287518738034704321069331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3066866539036846091406197 287518738034704321069331)
                ·
                  refine ⟨431278107052056481603997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287518738034704321069331 431278107052056481603997)
                  ·
                    refine ⟨161729290144521180601499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431278107052056481603997 161729290144521180601499)
                    ·
                      rfl

theorem cell22_472450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_472450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472450 prefixEnd_472450 := by exact prefixLift 472450
  have htrace : WordTrace (prefixWord ++ tailWord_472450) baseStart_472450 baseEnd_472450 := by
    simpa [prefixWord, tailWord_472450, baseEnd_472450] using wordTrace_append hprefix tailTrace_472450
  have hstable : (prefixWord ++ tailWord_472450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472450).length < 2 ^ (prefixWord ++ tailWord_472450).sum := by decide
  have hdescent : baseEnd_472450 < baseStart_472450 := by decide
  rcases family_descends (prefixWord ++ tailWord_472450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472459 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 1, 4]
def baseStart_472459 : Nat := 118140960795 + 472459 * 2 ^ 59
def prefixEnd_472459 : Nat := 4983230072969 + 3 ^ 40 * 472459 * 2
def baseEnd_472459 : Nat := 161732371028448157126471

theorem tailTrace_472459 : CollatzResearch.WordTrace tailWord_472459 prefixEnd_472459 161732371028448157126471 := by
  unfold tailWord_472459
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231995395369207418284431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11487996930246138278856287 17231995395369207418284431)
  ·
    refine ⟨25847993093053811127426647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231995395369207418284431 25847993093053811127426647)
    ·
      refine ⟨38771989639580716691139971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25847993093053811127426647 38771989639580716691139971)
      ·
        refine ⟨58157984459371075036709957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38771989639580716691139971 58157984459371075036709957)
        ·
          refine ⟨10904622086132076569383117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58157984459371075036709957 10904622086132076569383117)
          ·
            refine ⟨4089233282299528713518669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10904622086132076569383117 4089233282299528713518669)
            ·
              refine ⟨1533462480862323267569501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4089233282299528713518669 1533462480862323267569501)
              ·
                refine ⟨575048430323371225338563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1533462480862323267569501 575048430323371225338563)
                ·
                  refine ⟨862572645485056838007845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575048430323371225338563 862572645485056838007845)
                  ·
                    refine ⟨161732371028448157126471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862572645485056838007845 161732371028448157126471)
                    ·
                      rfl

theorem cell22_472459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_472459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472459 prefixEnd_472459 := by exact prefixLift 472459
  have htrace : WordTrace (prefixWord ++ tailWord_472459) baseStart_472459 baseEnd_472459 := by
    simpa [prefixWord, tailWord_472459, baseEnd_472459] using wordTrace_append hprefix tailTrace_472459
  have hstable : (prefixWord ++ tailWord_472459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472459).length < 2 ^ (prefixWord ++ tailWord_472459).sum := by decide
  have hdescent : baseEnd_472459 < baseStart_472459 := by decide
  rcases family_descends (prefixWord ++ tailWord_472459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472474 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_472474 : Nat := 118140960795 + 472474 * 2 ^ 59
def prefixEnd_472474 : Nat := 4983230072969 + 3 ^ 40 * 472474 * 2
def baseEnd_472474 : Nat := 53912501944997706000475

theorem tailTrace_472474 : CollatzResearch.WordTrace tailWord_472474 prefixEnd_472474 53912501944997706000475 := by
  unfold tailWord_472474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308135622578716245020119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11488361660209909986720317 4308135622578716245020119)
  ·
    refine ⟨6462203433868074367530179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308135622578716245020119 6462203433868074367530179)
    ·
      refine ⟨9693305150802111551295269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462203433868074367530179 9693305150802111551295269)
      ·
        refine ⟨1817494715775395915867863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9693305150802111551295269 1817494715775395915867863)
        ·
          refine ⟨2726242073663093873801795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817494715775395915867863 2726242073663093873801795)
          ·
            refine ⟨4089363110494640810702693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726242073663093873801795 4089363110494640810702693)
            ·
              refine ⟨766755583217745152006755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4089363110494640810702693 766755583217745152006755)
              ·
                refine ⟨1150133374826617728010133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766755583217745152006755 1150133374826617728010133)
                ·
                  refine ⟨53912501944997706000475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1150133374826617728010133 53912501944997706000475)
                  ·
                    rfl

theorem cell22_472474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_472474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472474 prefixEnd_472474 := by exact prefixLift 472474
  have htrace : WordTrace (prefixWord ++ tailWord_472474) baseStart_472474 baseEnd_472474 := by
    simpa [prefixWord, tailWord_472474, baseEnd_472474] using wordTrace_append hprefix tailTrace_472474
  have hstable : (prefixWord ++ tailWord_472474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472474).length < 2 ^ (prefixWord ++ tailWord_472474).sum := by decide
  have hdescent : baseEnd_472474 < baseStart_472474 := by decide
  rcases family_descends (prefixWord ++ tailWord_472474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472493 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_472493 : Nat := 118140960795 + 472493 * 2 ^ 59
def prefixEnd_472493 : Nat := 4983230072969 + 3 ^ 40 * 472493 * 2
def baseEnd_472493 : Nat := 161744009923283401776367

theorem tailTrace_472493 : CollatzResearch.WordTrace tailWord_472493 prefixEnd_472493 161744009923283401776367 := by
  unfold tailWord_472493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17233235477246031225022133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11488823651497354150014755 17233235477246031225022133)
  ·
    refine ⟨1615615825991815427345825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17233235477246031225022133 1615615825991815427345825)
    ·
      refine ⟨1211711869493861570509369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1615615825991815427345825 1211711869493861570509369)
      ·
        refine ⟨908783902120396177882027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211711869493861570509369 908783902120396177882027)
        ·
          refine ⟨1363175853180594266823041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908783902120396177882027 1363175853180594266823041)
          ·
            refine ⟨1022381889885445700117281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363175853180594266823041 1022381889885445700117281)
            ·
              refine ⟨766786417414084275087961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022381889885445700117281 766786417414084275087961)
              ·
                refine ⟨575089813060563206315971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766786417414084275087961 575089813060563206315971)
                ·
                  refine ⟨862634719590844809473957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575089813060563206315971 862634719590844809473957)
                  ·
                    refine ⟨161744009923283401776367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 862634719590844809473957 161744009923283401776367)
                    ·
                      rfl

theorem cell22_472493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_472493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472493 prefixEnd_472493 := by exact prefixLift 472493
  have htrace : WordTrace (prefixWord ++ tailWord_472493) baseStart_472493 baseEnd_472493 := by
    simpa [prefixWord, tailWord_472493, baseEnd_472493] using wordTrace_append hprefix tailTrace_472493
  have hstable : (prefixWord ++ tailWord_472493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472493).length < 2 ^ (prefixWord ++ tailWord_472493).sum := by decide
  have hdescent : baseEnd_472493 < baseStart_472493 := by decide
  rcases family_descends (prefixWord ++ tailWord_472493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472609 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 8]
def baseStart_472609 : Nat := 118140960795 + 472609 * 2 ^ 59
def prefixEnd_472609 : Nat := 4983230072969 + 3 ^ 40 * 472609 * 2
def baseEnd_472609 : Nat := 53927906364632588625337

theorem tailTrace_472609 : CollatzResearch.WordTrace tailWord_472609 prefixEnd_472609 53927906364632588625337 := by
  unfold tailWord_472609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237466344825783036244881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11491644229883855357496587 17237466344825783036244881)
  ·
    refine ⟨12928099758619337277183661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17237466344825783036244881 12928099758619337277183661)
    ·
      refine ⟨4848037409482251478943873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12928099758619337277183661 4848037409482251478943873)
      ·
        refine ⟨3636028057111688609207905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848037409482251478943873 3636028057111688609207905)
        ·
          refine ⟨2727021042833766456905929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3636028057111688609207905 2727021042833766456905929)
          ·
            refine ⟨2045265782125324842679447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727021042833766456905929 2045265782125324842679447)
            ·
              refine ⟨3067898673187987264019171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045265782125324842679447 3067898673187987264019171)
              ·
                refine ⟨4601848009781980896028757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067898673187987264019171 4601848009781980896028757)
                ·
                  refine ⟨53927906364632588625337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4601848009781980896028757 53927906364632588625337)
                  ·
                    rfl

theorem cell22_472609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_472609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472609 prefixEnd_472609 := by exact prefixLift 472609
  have htrace : WordTrace (prefixWord ++ tailWord_472609) baseStart_472609 baseEnd_472609 := by
    simpa [prefixWord, tailWord_472609, baseEnd_472609] using wordTrace_append hprefix tailTrace_472609
  have hstable : (prefixWord ++ tailWord_472609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472609).length < 2 ^ (prefixWord ++ tailWord_472609).sum := by decide
  have hdescent : baseEnd_472609 < baseStart_472609 := by decide
  rcases family_descends (prefixWord ++ tailWord_472609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472654 : List Nat := [4, 1, 1, 1, 1, 2, 1, 11]
def baseStart_472654 : Nat := 118140960795 + 472654 * 2 ^ 59
def prefixEnd_472654 : Nat := 4983230072969 + 3 ^ 40 * 472654 * 2
def baseEnd_472654 : Nat := 17977680390392516500097

theorem tailTrace_472654 : CollatzResearch.WordTrace tailWord_472654 prefixEnd_472654 17977680390392516500097 := by
  unfold tailWord_472654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154888453707844465204127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11492738419775170481088677 2154888453707844465204127)
  ·
    refine ⟨3232332680561766697806191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154888453707844465204127 3232332680561766697806191)
    ·
      refine ⟨4848499020842650046709287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232332680561766697806191 4848499020842650046709287)
      ·
        refine ⟨7272748531263975070063931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848499020842650046709287 7272748531263975070063931)
        ·
          refine ⟨10909122796895962605095897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272748531263975070063931 10909122796895962605095897)
          ·
            refine ⟨8181842097671971953821923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10909122796895962605095897 8181842097671971953821923)
            ·
              refine ⟨12272763146507957930732885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181842097671971953821923 12272763146507957930732885)
              ·
                refine ⟨17977680390392516500097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12272763146507957930732885 17977680390392516500097)
                ·
                  rfl

theorem cell22_472654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_472654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472654 prefixEnd_472654 := by exact prefixLift 472654
  have htrace : WordTrace (prefixWord ++ tailWord_472654) baseStart_472654 baseEnd_472654 := by
    simpa [prefixWord, tailWord_472654, baseEnd_472654] using wordTrace_append hprefix tailTrace_472654
  have hstable : (prefixWord ++ tailWord_472654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472654).length < 2 ^ (prefixWord ++ tailWord_472654).sum := by decide
  have hdescent : baseEnd_472654 < baseStart_472654 := by decide
  rcases family_descends (prefixWord ++ tailWord_472654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472658 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_472658 : Nat := 118140960795 + 472658 * 2 ^ 59
def prefixEnd_472658 : Nat := 4983230072969 + 3 ^ 40 * 472658 * 2
def baseEnd_472658 : Nat := 161800492795277971400861

theorem tailTrace_472658 : CollatzResearch.WordTrace tailWord_472658 prefixEnd_472658 161800492795277971400861 := by
  unfold tailWord_472658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309813380412066101194657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11492835681098842936519085 4309813380412066101194657)
  ·
    refine ⟨3232360035309049575895993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4309813380412066101194657 3232360035309049575895993)
    ·
      refine ⟨2424270026481787181921995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232360035309049575895993 2424270026481787181921995)
      ·
        refine ⟨3636405039722680772882993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424270026481787181921995 3636405039722680772882993)
        ·
          refine ⟨2727303779792010579662245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3636405039722680772882993 2727303779792010579662245)
          ·
            refine ⟨511369458711001983686671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2727303779792010579662245 511369458711001983686671)
            ·
              refine ⟨767054188066502975530007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511369458711001983686671 767054188066502975530007)
              ·
                refine ⟨1150581282099754463295011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767054188066502975530007 1150581282099754463295011)
                ·
                  refine ⟨1725871923149631694942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150581282099754463295011 1725871923149631694942517)
                  ·
                    refine ⟨161800492795277971400861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1725871923149631694942517 161800492795277971400861)
                    ·
                      rfl

theorem cell22_472658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_472658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472658 prefixEnd_472658 := by exact prefixLift 472658
  have htrace : WordTrace (prefixWord ++ tailWord_472658) baseStart_472658 baseEnd_472658 := by
    simpa [prefixWord, tailWord_472658, baseEnd_472658] using wordTrace_append hprefix tailTrace_472658
  have hstable : (prefixWord ++ tailWord_472658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472658).length < 2 ^ (prefixWord ++ tailWord_472658).sum := by decide
  have hdescent : baseEnd_472658 < baseStart_472658 := by decide
  rcases family_descends (prefixWord ++ tailWord_472658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472684 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_472684 : Nat := 118140960795 + 472684 * 2 ^ 59
def prefixEnd_472684 : Nat := 4983230072969 + 3 ^ 40 * 472684 * 2
def baseEnd_472684 : Nat := 161809393126622570250781

theorem tailTrace_472684 : CollatzResearch.WordTrace tailWord_472684 prefixEnd_472684 161809393126622570250781 := by
  unfold tailWord_472684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620100909777035422612553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11493467879702713896816737 8620100909777035422612553)
  ·
    refine ⟨6465075682332776566959415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8620100909777035422612553 6465075682332776566959415)
    ·
      refine ⟨9697613523499164850439123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465075682332776566959415 9697613523499164850439123)
      ·
        refine ⟨14546420285248747275658685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697613523499164850439123 14546420285248747275658685)
        ·
          refine ⟨5454907606968280228372007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14546420285248747275658685 5454907606968280228372007)
          ·
            refine ⟨8182361410452420342558011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454907606968280228372007 8182361410452420342558011)
            ·
              refine ⟨12273542115678630513837017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182361410452420342558011 12273542115678630513837017)
              ·
                refine ⟨9205156586758972885377763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273542115678630513837017 9205156586758972885377763)
                ·
                  refine ⟨13807734880138459328066645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205156586758972885377763 13807734880138459328066645)
                  ·
                    refine ⟨161809393126622570250781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13807734880138459328066645 161809393126622570250781)
                    ·
                      rfl

theorem cell22_472684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_472684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472684 prefixEnd_472684 := by exact prefixLift 472684
  have htrace : WordTrace (prefixWord ++ tailWord_472684) baseStart_472684 baseEnd_472684 := by
    simpa [prefixWord, tailWord_472684, baseEnd_472684] using wordTrace_append hprefix tailTrace_472684
  have hstable : (prefixWord ++ tailWord_472684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472684).length < 2 ^ (prefixWord ++ tailWord_472684).sum := by decide
  have hdescent : baseEnd_472684 < baseStart_472684 := by decide
  rcases family_descends (prefixWord ++ tailWord_472684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472699 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 7]
def baseStart_472699 : Nat := 118140960795 + 472699 * 2 ^ 59
def prefixEnd_472699 : Nat := 4983230072969 + 3 ^ 40 * 472699 * 2
def baseEnd_472699 : Nat := 53938175977722510375245

theorem tailTrace_472699 : CollatzResearch.WordTrace tailWord_472699 prefixEnd_472699 53938175977722510375245 := by
  unfold tailWord_472699
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240748914499728407021151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11493832609666485604680767 17240748914499728407021151)
  ·
    refine ⟨25861123371749592610531727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17240748914499728407021151 25861123371749592610531727)
    ·
      refine ⟨38791685057624388915797591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25861123371749592610531727 38791685057624388915797591)
      ·
        refine ⟨58187527586436583373696387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38791685057624388915797591 58187527586436583373696387)
        ·
          refine ⟨87281291379654875060544581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58187527586436583373696387 87281291379654875060544581)
          ·
            refine ⟨16365242133685289073852109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87281291379654875060544581 16365242133685289073852109)
            ·
              refine ⟨6136965800131983402694541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365242133685289073852109 6136965800131983402694541)
              ·
                refine ⟨2301362175049493776010453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6136965800131983402694541 2301362175049493776010453)
                ·
                  refine ⟨53938175977722510375245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2301362175049493776010453 53938175977722510375245)
                  ·
                    rfl

theorem cell22_472699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_472699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472699 prefixEnd_472699 := by exact prefixLift 472699
  have htrace : WordTrace (prefixWord ++ tailWord_472699) baseStart_472699 baseEnd_472699 := by
    simpa [prefixWord, tailWord_472699, baseEnd_472699] using wordTrace_append hprefix tailTrace_472699
  have hstable : (prefixWord ++ tailWord_472699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472699).length < 2 ^ (prefixWord ++ tailWord_472699).sum := by decide
  have hdescent : baseEnd_472699 < baseStart_472699 := by decide
  rcases family_descends (prefixWord ++ tailWord_472699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472716 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_472716 : Nat := 118140960795 + 472716 * 2 ^ 59
def prefixEnd_472716 : Nat := 4983230072969 + 3 ^ 40 * 472716 * 2
def baseEnd_472716 : Nat := 53940115793528384483561

theorem tailTrace_472716 : CollatzResearch.WordTrace tailWord_472716 prefixEnd_472716 53940115793528384483561 := by
  unfold tailWord_472716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620684477719070155195001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11494245970292093540260001 8620684477719070155195001)
  ·
    refine ⟨6465513358289302616396251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8620684477719070155195001 6465513358289302616396251)
    ·
      refine ⟨9698270037433953924594377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465513358289302616396251 9698270037433953924594377)
      ·
        refine ⟨7273702528075465443445783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9698270037433953924594377 7273702528075465443445783)
        ·
          refine ⟨10910553792113198165168675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273702528075465443445783 10910553792113198165168675)
          ·
            refine ⟨16365830688169797247753013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910553792113198165168675 16365830688169797247753013)
            ·
              refine ⟨1534296627015918491976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16365830688169797247753013 1534296627015918491976845)
              ·
                refine ⟨575361235130969434491317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534296627015918491976845 575361235130969434491317)
                ·
                  refine ⟨53940115793528384483561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575361235130969434491317 53940115793528384483561)
                  ·
                    rfl

theorem cell22_472716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_472716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472716 prefixEnd_472716 := by exact prefixLift 472716
  have htrace : WordTrace (prefixWord ++ tailWord_472716) baseStart_472716 baseEnd_472716 := by
    simpa [prefixWord, tailWord_472716, baseEnd_472716] using wordTrace_append hprefix tailTrace_472716
  have hstable : (prefixWord ++ tailWord_472716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472716).length < 2 ^ (prefixWord ++ tailWord_472716).sum := by decide
  have hdescent : baseEnd_472716 < baseStart_472716 := by decide
  rcases family_descends (prefixWord ++ tailWord_472716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472778 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_472778 : Nat := 118140960795 + 472778 * 2 ^ 59
def prefixEnd_472778 : Nat := 4983230072969 + 3 ^ 40 * 472778 * 2
def baseEnd_472778 : Nat := 53947190415879219466831

theorem tailTrace_472778 : CollatzResearch.WordTrace tailWord_472778 prefixEnd_472778 53947190415879219466831 := by
  unfold tailWord_472778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310907570303381224786747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11495753520809016599431325 4310907570303381224786747)
  ·
    refine ⟨6466361355455071837180121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310907570303381224786747 6466361355455071837180121)
    ·
      refine ⟨4849771016591303877885091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6466361355455071837180121 4849771016591303877885091)
      ·
        refine ⟨7274656524886955816827637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849771016591303877885091 7274656524886955816827637)
        ·
          refine ⟨681999049208152107827591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7274656524886955816827637 681999049208152107827591)
          ·
            refine ⟨1022998573812228161741387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681999049208152107827591 1022998573812228161741387)
            ·
              refine ⟨1534497860718342242612081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022998573812228161741387 1534497860718342242612081)
              ·
                refine ⟨1150873395538756681959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534497860718342242612081 1150873395538756681959061)
                ·
                  refine ⟨53947190415879219466831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1150873395538756681959061 53947190415879219466831)
                  ·
                    rfl

theorem cell22_472778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_472778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472778 prefixEnd_472778 := by exact prefixLift 472778
  have htrace : WordTrace (prefixWord ++ tailWord_472778) baseStart_472778 baseEnd_472778 := by
    simpa [prefixWord, tailWord_472778, baseEnd_472778] using wordTrace_append hprefix tailTrace_472778
  have hstable : (prefixWord ++ tailWord_472778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472778).length < 2 ^ (prefixWord ++ tailWord_472778).sum := by decide
  have hdescent : baseEnd_472778 < baseStart_472778 := by decide
  rcases family_descends (prefixWord ++ tailWord_472778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472791 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_472791 : Nat := 118140960795 + 472791 * 2 ^ 59
def prefixEnd_472791 : Nat := 4983230072969 + 3 ^ 40 * 472791 * 2
def baseEnd_472791 : Nat := 161846021413309957825453

theorem tailTrace_472791 : CollatzResearch.WordTrace tailWord_472791 prefixEnd_472791 161846021413309957825453 := by
  unfold tailWord_472791
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244104430166428119370227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11496069620110952079580151 17244104430166428119370227)
  ·
    refine ⟨25866156645249642179055341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17244104430166428119370227 25866156645249642179055341)
    ·
      refine ⟨9699808741968615817145753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25866156645249642179055341 9699808741968615817145753)
      ·
        refine ⟨7274856556476461862859315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9699808741968615817145753 7274856556476461862859315)
        ·
          refine ⟨10912284834714692794288973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274856556476461862859315 10912284834714692794288973)
          ·
            refine ⟨4092106813018009797858365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10912284834714692794288973 4092106813018009797858365)
            ·
              refine ⟨1534540054881753674196887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4092106813018009797858365 1534540054881753674196887)
              ·
                refine ⟨2301810082322630511295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534540054881753674196887 2301810082322630511295331)
                ·
                  refine ⟨3452715123483945766942997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301810082322630511295331 3452715123483945766942997)
                  ·
                    refine ⟨161846021413309957825453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3452715123483945766942997 161846021413309957825453)
                    ·
                      rfl

theorem cell22_472791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_472791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472791 prefixEnd_472791 := by exact prefixLift 472791
  have htrace : WordTrace (prefixWord ++ tailWord_472791) baseStart_472791 baseEnd_472791 := by
    simpa [prefixWord, tailWord_472791, baseEnd_472791] using wordTrace_append hprefix tailTrace_472791
  have hstable : (prefixWord ++ tailWord_472791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472791).length < 2 ^ (prefixWord ++ tailWord_472791).sum := by decide
  have hdescent : baseEnd_472791 < baseStart_472791 := by decide
  rcases family_descends (prefixWord ++ tailWord_472791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472797 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_472797 : Nat := 118140960795 + 472797 * 2 ^ 59
def prefixEnd_472797 : Nat := 4983230072969 + 3 ^ 40 * 472797 * 2
def baseEnd_472797 : Nat := 161848075335927942175435

theorem tailTrace_472797 : CollatzResearch.WordTrace tailWord_472797 prefixEnd_472797 161848075335927942175435 := by
  unfold tailWord_472797
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244323268144691144088645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11496215512096460762725763 17244323268144691144088645)
  ·
    refine ⟨3233310612777129589516621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17244323268144691144088645 3233310612777129589516621)
    ·
      refine ⟨1212491479791423596068733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3233310612777129589516621 1212491479791423596068733)
      ·
        refine ⟨454684304921783848525775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1212491479791423596068733 454684304921783848525775)
        ·
          refine ⟨682026457382675772788663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454684304921783848525775 682026457382675772788663)
          ·
            refine ⟨1023039686074013659182995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682026457382675772788663 1023039686074013659182995)
            ·
              refine ⟨1534559529111020488774493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023039686074013659182995 1534559529111020488774493)
              ·
                refine ⟨575459823416632683290435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534559529111020488774493 575459823416632683290435)
                ·
                  refine ⟨863189735124949024935653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575459823416632683290435 863189735124949024935653)
                  ·
                    refine ⟨161848075335927942175435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863189735124949024935653 161848075335927942175435)
                    ·
                      rfl

theorem cell22_472797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_472797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472797 prefixEnd_472797 := by exact prefixLift 472797
  have htrace : WordTrace (prefixWord ++ tailWord_472797) baseStart_472797 baseEnd_472797 := by
    simpa [prefixWord, tailWord_472797, baseEnd_472797] using wordTrace_append hprefix tailTrace_472797
  have hstable : (prefixWord ++ tailWord_472797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472797).length < 2 ^ (prefixWord ++ tailWord_472797).sum := by decide
  have hdescent : baseEnd_472797 < baseStart_472797 := by decide
  rcases family_descends (prefixWord ++ tailWord_472797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472810 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_472810 : Nat := 118140960795 + 472810 * 2 ^ 59
def prefixEnd_472810 : Nat := 4983230072969 + 3 ^ 40 * 472810 * 2
def baseEnd_472810 : Nat := 161852525501600241600395

theorem tailTrace_472810 : CollatzResearch.WordTrace tailWord_472810 prefixEnd_472810 161852525501600241600395 := by
  unfold tailWord_472810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311199354274398591077971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11496531611398396242874589 4311199354274398591077971)
  ·
    refine ⟨6466799031411597886616957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311199354274398591077971 6466799031411597886616957)
    ·
      refine ⟨2425049636779349207481359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6466799031411597886616957 2425049636779349207481359)
      ·
        refine ⟨3637574455169023811222039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425049636779349207481359 3637574455169023811222039)
        ·
          refine ⟨5456361682753535716833059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637574455169023811222039 5456361682753535716833059)
          ·
            refine ⟨8184542524130303575249589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456361682753535716833059 8184542524130303575249589)
            ·
              refine ⟨767300861637215960179649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8184542524130303575249589 767300861637215960179649)
              ·
                refine ⟨575475646227911970134737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767300861637215960179649 575475646227911970134737)
                ·
                  refine ⟨431606734670933977601053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575475646227911970134737 431606734670933977601053)
                  ·
                    refine ⟨161852525501600241600395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431606734670933977601053 161852525501600241600395)
                    ·
                      rfl

theorem cell22_472810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_472810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472810 prefixEnd_472810 := by exact prefixLift 472810
  have htrace : WordTrace (prefixWord ++ tailWord_472810) baseStart_472810 baseEnd_472810 := by
    simpa [prefixWord, tailWord_472810, baseEnd_472810] using wordTrace_append hprefix tailTrace_472810
  have hstable : (prefixWord ++ tailWord_472810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472810).length < 2 ^ (prefixWord ++ tailWord_472810).sum := by decide
  have hdescent : baseEnd_472810 < baseStart_472810 := by decide
  rcases family_descends (prefixWord ++ tailWord_472810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472868 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_472868 : Nat := 118140960795 + 472868 * 2 ^ 59
def prefixEnd_472868 : Nat := 4983230072969 + 3 ^ 40 * 472868 * 2
def baseEnd_472868 : Nat := 53957460028969141216739

theorem tailTrace_472868 : CollatzResearch.WordTrace tailWord_472868 prefixEnd_472868 53957460028969141216739 := by
  unfold tailWord_472868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623456425443735134961629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11497941900591646846615505 8623456425443735134961629)
  ·
    refine ⟨3233796159541400675610611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8623456425443735134961629 3233796159541400675610611)
    ·
      refine ⟨4850694239312101013415917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233796159541400675610611 4850694239312101013415917)
      ·
        refine ⟨1819010339742037880030969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4850694239312101013415917 1819010339742037880030969)
        ·
          refine ⟨1364257754806528410023227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819010339742037880030969 1364257754806528410023227)
          ·
            refine ⟨2046386632209792615034841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364257754806528410023227 2046386632209792615034841)
            ·
              refine ⟨1534789974157344461276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046386632209792615034841 1534789974157344461276131)
              ·
                refine ⟨2302184961236016691914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534789974157344461276131 2302184961236016691914197)
                ·
                  refine ⟨53957460028969141216739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2302184961236016691914197 53957460028969141216739)
                  ·
                    rfl

theorem cell22_472868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_472868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472868 prefixEnd_472868 := by exact prefixLift 472868
  have htrace : WordTrace (prefixWord ++ tailWord_472868) baseStart_472868 baseEnd_472868 := by
    simpa [prefixWord, tailWord_472868, baseEnd_472868] using wordTrace_append hprefix tailTrace_472868
  have hstable : (prefixWord ++ tailWord_472868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472868).length < 2 ^ (prefixWord ++ tailWord_472868).sum := by decide
  have hdescent : baseEnd_472868 < baseStart_472868 := by decide
  rcases family_descends (prefixWord ++ tailWord_472868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472872 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_472872 : Nat := 118140960795 + 472872 * 2 ^ 59
def prefixEnd_472872 : Nat := 4983230072969 + 3 ^ 40 * 472872 * 2
def baseEnd_472872 : Nat := 161873749368652746550205

theorem tailTrace_472872 : CollatzResearch.WordTrace tailWord_472872 prefixEnd_472872 161873749368652746550205 := by
  unfold tailWord_472872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623529371436489476534435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11498039161915319302045913 8623529371436489476534435)
  ·
    refine ⟨12935294057154734214801653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8623529371436489476534435 12935294057154734214801653)
    ·
      refine ⟨1212683817858256332637655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12935294057154734214801653 1212683817858256332637655)
      ·
        refine ⟨1819025726787384498956483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212683817858256332637655 1819025726787384498956483)
        ·
          refine ⟨2728538590181076748434725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819025726787384498956483 2728538590181076748434725)
          ·
            refine ⟨511600985658951890331511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2728538590181076748434725 511600985658951890331511)
            ·
              refine ⟨767401478488427835497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511600985658951890331511 767401478488427835497267)
              ·
                refine ⟨1151102217732641753245901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767401478488427835497267 1151102217732641753245901)
                ·
                  refine ⟨431663331649740657467213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151102217732641753245901 431663331649740657467213)
                  ·
                    refine ⟨161873749368652746550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431663331649740657467213 161873749368652746550205)
                    ·
                      rfl

theorem cell22_472872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_472872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472872 prefixEnd_472872 := by exact prefixLift 472872
  have htrace : WordTrace (prefixWord ++ tailWord_472872) baseStart_472872 baseEnd_472872 := by
    simpa [prefixWord, tailWord_472872, baseEnd_472872] using wordTrace_append hprefix tailTrace_472872
  have hstable : (prefixWord ++ tailWord_472872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472872).length < 2 ^ (prefixWord ++ tailWord_472872).sum := by decide
  have hdescent : baseEnd_472872 < baseStart_472872 := by decide
  rcases family_descends (prefixWord ++ tailWord_472872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472885 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 5]
def baseStart_472885 : Nat := 118140960795 + 472885 * 2 ^ 59
def prefixEnd_472885 : Nat := 4983230072969 + 3 ^ 40 * 472885 * 2
def baseEnd_472885 : Nat := 53959399844775015325055

theorem tailTrace_472885 : CollatzResearch.WordTrace tailWord_472885 prefixEnd_472885 53959399844775015325055 := by
  unfold tailWord_472885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247532891825882173292109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11498355261217254782194739 17247532891825882173292109)
  ·
    refine ⟨6467824834434705814984541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17247532891825882173292109 6467824834434705814984541)
    ·
      refine ⟨2425434312913014680619203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6467824834434705814984541 2425434312913014680619203)
      ·
        refine ⟨3638151469369522020928805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425434312913014680619203 3638151469369522020928805)
        ·
          refine ⟨682153400506785378924151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3638151469369522020928805 682153400506785378924151)
          ·
            refine ⟨1023230100760178068386227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682153400506785378924151 1023230100760178068386227)
            ·
              refine ⟨1534845151140267102579341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023230100760178068386227 1534845151140267102579341)
              ·
                refine ⟨575566931677600163467253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534845151140267102579341 575566931677600163467253)
                ·
                  refine ⟨53959399844775015325055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575566931677600163467253 53959399844775015325055)
                  ·
                    rfl

theorem cell22_472885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_472885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472885 prefixEnd_472885 := by exact prefixLift 472885
  have htrace : WordTrace (prefixWord ++ tailWord_472885) baseStart_472885 baseEnd_472885 := by
    simpa [prefixWord, tailWord_472885, baseEnd_472885] using wordTrace_append hprefix tailTrace_472885
  have hstable : (prefixWord ++ tailWord_472885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472885).length < 2 ^ (prefixWord ++ tailWord_472885).sum := by decide
  have hdescent : baseEnd_472885 < baseStart_472885 := by decide
  rcases family_descends (prefixWord ++ tailWord_472885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472945 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_472945 : Nat := 118140960795 + 472945 * 2 ^ 59
def prefixEnd_472945 : Nat := 4983230072969 + 3 ^ 40 * 472945 * 2
def baseEnd_472945 : Nat := 161898738760504889474981

theorem tailTrace_472945 : CollatzResearch.WordTrace tailWord_472945 prefixEnd_472945 161898738760504889474981 := by
  unfold tailWord_472945
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249721271608512420476289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11499814181072341613650859 17249721271608512420476289)
  ·
    refine ⟨12937290953706384315357217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17249721271608512420476289 12937290953706384315357217)
    ·
      refine ⟨9702968215279788236517913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12937290953706384315357217 9702968215279788236517913)
      ·
        refine ⟨7277226161459841177388435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9702968215279788236517913 7277226161459841177388435)
        ·
          refine ⟨10915839242189761766082653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277226161459841177388435 10915839242189761766082653)
          ·
            refine ⟨4093439715821160662280995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10915839242189761766082653 4093439715821160662280995)
            ·
              refine ⟨6140159573731740993421493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093439715821160662280995 6140159573731740993421493)
              ·
                refine ⟨575639960037350718133265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6140159573731740993421493 575639960037350718133265)
                ·
                  refine ⟨431729970028013038599949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575639960037350718133265 431729970028013038599949)
                  ·
                    refine ⟨161898738760504889474981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431729970028013038599949 161898738760504889474981)
                    ·
                      rfl

theorem cell22_472945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_472945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_472945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_472945 prefixEnd_472945 := by exact prefixLift 472945
  have htrace : WordTrace (prefixWord ++ tailWord_472945) baseStart_472945 baseEnd_472945 := by
    simpa [prefixWord, tailWord_472945, baseEnd_472945] using wordTrace_append hprefix tailTrace_472945
  have hstable : (prefixWord ++ tailWord_472945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472945).length < 2 ^ (prefixWord ++ tailWord_472945).sum := by decide
  have hdescent : baseEnd_472945 < baseStart_472945 := by decide
  rcases family_descends (prefixWord ++ tailWord_472945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473018 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_473018 : Nat := 118140960795 + 473018 * 2 ^ 59
def prefixEnd_473018 : Nat := 4983230072969 + 3 ^ 40 * 473018 * 2
def baseEnd_473018 : Nat := 161923728152357032399757

theorem tailTrace_473018 : CollatzResearch.WordTrace tailWord_473018 prefixEnd_473018 161923728152357032399757 := by
  unfold tailWord_473018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313095950086011471970927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11501589200229363925255805 4313095950086011471970927)
  ·
    refine ⟨6469643925129017207956391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313095950086011471970927 6469643925129017207956391)
    ·
      refine ⟨9704465887693525811934587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469643925129017207956391 9704465887693525811934587)
      ·
        refine ⟨14556698831540288717901881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704465887693525811934587 14556698831540288717901881)
        ·
          refine ⟨10917524123655216538426411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14556698831540288717901881 10917524123655216538426411)
          ·
            refine ⟨16376286185482824807639617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917524123655216538426411 16376286185482824807639617)
            ·
              refine ⟨12282214639112118605729713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376286185482824807639617 12282214639112118605729713)
              ·
                refine ⟨9211660979334088954297285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282214639112118605729713 9211660979334088954297285)
                ·
                  refine ⟨1727186433625141678930741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9211660979334088954297285 1727186433625141678930741)
                  ·
                    refine ⟨161923728152357032399757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1727186433625141678930741 161923728152357032399757)
                    ·
                      rfl

theorem cell22_473018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_473018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473018 prefixEnd_473018 := by exact prefixLift 473018
  have htrace : WordTrace (prefixWord ++ tailWord_473018) baseStart_473018 baseEnd_473018 := by
    simpa [prefixWord, tailWord_473018, baseEnd_473018] using wordTrace_append hprefix tailTrace_473018
  have hstable : (prefixWord ++ tailWord_473018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473018).length < 2 ^ (prefixWord ++ tailWord_473018).sum := by decide
  have hdescent : baseEnd_473018 < baseStart_473018 := by decide
  rcases family_descends (prefixWord ++ tailWord_473018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473080 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_473080 : Nat := 118140960795 + 473080 * 2 ^ 59
def prefixEnd_473080 : Nat := 4983230072969 + 3 ^ 40 * 473080 * 2
def baseEnd_473080 : Nat := 161944952019409537349567

theorem tailTrace_473080 : CollatzResearch.WordTrace tailWord_473080 prefixEnd_473080 161944952019409537349567 := by
  unfold tailWord_473080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627322563059715238320347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11503096750746286984427129 8627322563059715238320347)
  ·
    refine ⟨12940983844589572857480521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627322563059715238320347 12940983844589572857480521)
    ·
      refine ⟨9705737883442179643110391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940983844589572857480521 9705737883442179643110391)
      ·
        refine ⟨14558606825163269464665587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705737883442179643110391 14558606825163269464665587)
        ·
          refine ⟨21837910237744904196998381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14558606825163269464665587 21837910237744904196998381)
          ·
            refine ⟨8189216339154339073874393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21837910237744904196998381 8189216339154339073874393)
            ·
              refine ⟨6141912254365754305405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189216339154339073874393 6141912254365754305405795)
              ·
                refine ⟨9212868381548631458108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141912254365754305405795 9212868381548631458108693)
                ·
                  refine ⟨431853205385092099598845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9212868381548631458108693 431853205385092099598845)
                  ·
                    refine ⟨161944952019409537349567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431853205385092099598845 161944952019409537349567)
                    ·
                      rfl

theorem cell22_473080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_473080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473080 prefixEnd_473080 := by exact prefixLift 473080
  have htrace : WordTrace (prefixWord ++ tailWord_473080) baseStart_473080 baseEnd_473080 := by
    simpa [prefixWord, tailWord_473080, baseEnd_473080] using wordTrace_append hprefix tailTrace_473080
  have hstable : (prefixWord ++ tailWord_473080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473080).length < 2 ^ (prefixWord ++ tailWord_473080).sum := by decide
  have hdescent : baseEnd_473080 < baseStart_473080 := by decide
  rcases family_descends (prefixWord ++ tailWord_473080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473093 : List Nat := [1, 3, 1, 1, 2, 14]
def baseStart_473093 : Nat := 118140960795 + 473093 * 2 ^ 59
def prefixEnd_473093 : Nat := 4983230072969 + 3 ^ 40 * 473093 * 2
def baseEnd_473093 : Nat := 1999375335618294281167

theorem tailTrace_473093 : CollatzResearch.WordTrace tailWord_473093 prefixEnd_473093 1999375335618294281167 := by
  unfold tailWord_473093
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255119275072333696863933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11503412850048222464575955 17255119275072333696863933)
  ·
    refine ⟨6470669728152125136323975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17255119275072333696863933 6470669728152125136323975)
    ·
      refine ⟨9706004592228187704485963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470669728152125136323975 9706004592228187704485963)
      ·
        refine ⟨14559006888342281556728945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706004592228187704485963 14559006888342281556728945)
        ·
          refine ⟨10919255166256711167546709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14559006888342281556728945 10919255166256711167546709)
          ·
            refine ⟨1999375335618294281167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 10919255166256711167546709 1999375335618294281167)
            ·
              rfl

theorem cell22_473093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 14].length) (baseStart_473093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473093 prefixEnd_473093 := by exact prefixLift 473093
  have htrace : WordTrace (prefixWord ++ tailWord_473093) baseStart_473093 baseEnd_473093 := by
    simpa [prefixWord, tailWord_473093, baseEnd_473093] using wordTrace_append hprefix tailTrace_473093
  have hstable : (prefixWord ++ tailWord_473093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473093).length < 2 ^ (prefixWord ++ tailWord_473093).sum := by decide
  have hdescent : baseEnd_473093 < baseStart_473093 := by decide
  rcases family_descends (prefixWord ++ tailWord_473093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473155 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 5]
def baseStart_473155 : Nat := 118140960795 + 473155 * 2 ^ 59
def prefixEnd_473155 : Nat := 4983230072969 + 3 ^ 40 * 473155 * 2
def baseEnd_473155 : Nat := 53990208684044780574779

theorem tailTrace_473155 : CollatzResearch.WordTrace tailWord_473155 prefixEnd_473155 53990208684044780574779 := by
  unfold tailWord_473155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257380600847718285620919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504920400565145523747279 17257380600847718285620919)
  ·
    refine ⟨25886070901271577428431379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17257380600847718285620919 25886070901271577428431379)
    ·
      refine ⟨38829106351907366142647069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25886070901271577428431379 38829106351907366142647069)
      ·
        refine ⟨14560914881965262303492651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38829106351907366142647069 14560914881965262303492651)
        ·
          refine ⟨21841372322947893455238977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14560914881965262303492651 21841372322947893455238977)
          ·
            refine ⟨16381029242210920091429233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21841372322947893455238977 16381029242210920091429233)
            ·
              refine ⟨12285771931658190068571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16381029242210920091429233 12285771931658190068571925)
              ·
                refine ⟨575895559296477659464309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12285771931658190068571925 575895559296477659464309)
                ·
                  refine ⟨53990208684044780574779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575895559296477659464309 53990208684044780574779)
                  ·
                    rfl

theorem cell22_473155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].length) (baseStart_473155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473155 prefixEnd_473155 := by exact prefixLift 473155
  have htrace : WordTrace (prefixWord ++ tailWord_473155) baseStart_473155 baseEnd_473155 := by
    simpa [prefixWord, tailWord_473155, baseEnd_473155] using wordTrace_append hprefix tailTrace_473155
  have hstable : (prefixWord ++ tailWord_473155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473155).length < 2 ^ (prefixWord ++ tailWord_473155).sum := by decide
  have hdescent : baseEnd_473155 < baseStart_473155 := by decide
  rcases family_descends (prefixWord ++ tailWord_473155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473159 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 1, 3]
def baseStart_473159 : Nat := 118140960795 + 473159 * 2 ^ 59
def prefixEnd_473159 : Nat := 4983230072969 + 3 ^ 40 * 473159 * 2
def baseEnd_473159 : Nat := 161971995333879664624325

theorem tailTrace_473159 : CollatzResearch.WordTrace tailWord_473159 prefixEnd_473159 161971995333879664624325 := by
  unfold tailWord_473159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257526492833226968766531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11505017661888817979177687 17257526492833226968766531)
  ·
    refine ⟨25886289739249840453149797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17257526492833226968766531 25886289739249840453149797)
    ·
      refine ⟨4853679326109345084965587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25886289739249840453149797 4853679326109345084965587)
      ·
        refine ⟨7280518989164017627448381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853679326109345084965587 7280518989164017627448381)
        ·
          refine ⟨2730194620936506610293143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7280518989164017627448381 2730194620936506610293143)
          ·
            refine ⟨4095291931404759915439715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730194620936506610293143 4095291931404759915439715)
            ·
              refine ⟨6142937897107139873159573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095291931404759915439715 6142937897107139873159573)
              ·
                refine ⟨287950213926897181554355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6142937897107139873159573 287950213926897181554355)
                ·
                  refine ⟨431925320890345772331533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287950213926897181554355 431925320890345772331533)
                  ·
                    refine ⟨161971995333879664624325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431925320890345772331533 161971995333879664624325)
                    ·
                      rfl

theorem cell22_473159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_473159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473159 prefixEnd_473159 := by exact prefixLift 473159
  have htrace : WordTrace (prefixWord ++ tailWord_473159) baseStart_473159 baseEnd_473159 := by
    simpa [prefixWord, tailWord_473159, baseEnd_473159] using wordTrace_append hprefix tailTrace_473159
  have hstable : (prefixWord ++ tailWord_473159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473159).length < 2 ^ (prefixWord ++ tailWord_473159).sum := by decide
  have hdescent : baseEnd_473159 < baseStart_473159 := by decide
  rcases family_descends (prefixWord ++ tailWord_473159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473236 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_473236 : Nat := 118140960795 + 473236 * 2 ^ 59
def prefixEnd_473236 : Nat := 4983230072969 + 3 ^ 40 * 473236 * 2
def baseEnd_473236 : Nat := 161998354007477130449089

theorem tailTrace_473236 : CollatzResearch.WordTrace tailWord_473236 prefixEnd_473236 161998354007477130449089 := by
  unfold tailWord_473236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630167456777134559659781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11506889942369512746213041 8630167456777134559659781)
  ·
    refine ⟨1618156398145712729936209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8630167456777134559659781 1618156398145712729936209)
    ·
      refine ⟨1213617298609284547452157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618156398145712729936209 1213617298609284547452157)
      ·
        refine ⟨455106486978481705294559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1213617298609284547452157 455106486978481705294559)
        ·
          refine ⟨682659730467722557941839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455106486978481705294559 682659730467722557941839)
          ·
            refine ⟨1023989595701583836912759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682659730467722557941839 1023989595701583836912759)
            ·
              refine ⟨1535984393552375755369139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023989595701583836912759 1535984393552375755369139)
              ·
                refine ⟨2303976590328563633053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535984393552375755369139 2303976590328563633053709)
                ·
                  refine ⟨863991221373211362395141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2303976590328563633053709 863991221373211362395141)
                  ·
                    refine ⟨161998354007477130449089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863991221373211362395141 161998354007477130449089)
                    ·
                      rfl

theorem cell22_473236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_473236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473236 prefixEnd_473236 := by exact prefixLift 473236
  have htrace : WordTrace (prefixWord ++ tailWord_473236) baseStart_473236 baseEnd_473236 := by
    simpa [prefixWord, tailWord_473236, baseEnd_473236] using wordTrace_append hprefix tailTrace_473236
  have hstable : (prefixWord ++ tailWord_473236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473236).length < 2 ^ (prefixWord ++ tailWord_473236).sum := by decide
  have hdescent : baseEnd_473236 < baseStart_473236 := by decide
  rcases family_descends (prefixWord ++ tailWord_473236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_473260 : Nat := 118140960795 + 473260 * 2 ^ 59
def prefixEnd_473260 : Nat := 4983230072969 + 3 ^ 40 * 473260 * 2
def baseEnd_473260 : Nat := 162006569697949067849015

theorem tailTrace_473260 : CollatzResearch.WordTrace tailWord_473260 prefixEnd_473260 162006569697949067849015 := by
  unfold tailWord_473260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630605132733660609096617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11507473510311547478795489 8630605132733660609096617)
  ·
    refine ⟨6472953849550245456822463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8630605132733660609096617 6472953849550245456822463)
    ·
      refine ⟨9709430774325368185233695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472953849550245456822463 9709430774325368185233695)
      ·
        refine ⟨14564146161488052277850543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709430774325368185233695 14564146161488052277850543)
        ·
          refine ⟨21846219242232078416775815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564146161488052277850543 21846219242232078416775815)
          ·
            refine ⟨32769328863348117625163723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21846219242232078416775815 32769328863348117625163723)
            ·
              refine ⟨49153993295022176437745585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32769328863348117625163723 49153993295022176437745585)
              ·
                refine ⟨36865494971266632328309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49153993295022176437745585 36865494971266632328309189)
                ·
                  refine ⟨6912280307112493561557973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36865494971266632328309189 6912280307112493561557973)
                  ·
                    refine ⟨162006569697949067849015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6912280307112493561557973 162006569697949067849015)
                    ·
                      rfl

theorem cell22_473260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_473260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473260 prefixEnd_473260 := by exact prefixLift 473260
  have htrace : WordTrace (prefixWord ++ tailWord_473260) baseStart_473260 baseEnd_473260 := by
    simpa [prefixWord, tailWord_473260, baseEnd_473260] using wordTrace_append hprefix tailTrace_473260
  have hstable : (prefixWord ++ tailWord_473260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473260).length < 2 ^ (prefixWord ++ tailWord_473260).sum := by decide
  have hdescent : baseEnd_473260 < baseStart_473260 := by decide
  rcases family_descends (prefixWord ++ tailWord_473260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473275 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_473275 : Nat := 118140960795 + 473275 * 2 ^ 59
def prefixEnd_473275 : Nat := 4983230072969 + 3 ^ 40 * 473275 * 2
def baseEnd_473275 : Nat := 162011704504494028723969

theorem tailTrace_473275 : CollatzResearch.WordTrace tailWord_473275 prefixEnd_473275 162011704504494028723969 := by
  unfold tailWord_473275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17261757360412978779989279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11507838240275319186659519 17261757360412978779989279)
  ·
    refine ⟨25892636040619468169983919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17261757360412978779989279 25892636040619468169983919)
    ·
      refine ⟨38838954060929202254975879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25892636040619468169983919 38838954060929202254975879)
      ·
        refine ⟨58258431091393803382463819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38838954060929202254975879 58258431091393803382463819)
        ·
          refine ⟨87387646637090705073695729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58258431091393803382463819 87387646637090705073695729)
          ·
            refine ⟨65540734977818028805271797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87387646637090705073695729 65540734977818028805271797)
            ·
              refine ⟨6144443904170440200494231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65540734977818028805271797 6144443904170440200494231)
              ·
                refine ⟨9216665856255660300741347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144443904170440200494231 9216665856255660300741347)
                ·
                  refine ⟨13824998784383490451112021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216665856255660300741347 13824998784383490451112021)
                  ·
                    refine ⟨162011704504494028723969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13824998784383490451112021 162011704504494028723969)
                    ·
                      rfl

theorem cell22_473275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_473275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473275 prefixEnd_473275 := by exact prefixLift 473275
  have htrace : WordTrace (prefixWord ++ tailWord_473275) baseStart_473275 baseEnd_473275 := by
    simpa [prefixWord, tailWord_473275, baseEnd_473275] using wordTrace_append hprefix tailTrace_473275
  have hstable : (prefixWord ++ tailWord_473275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473275).length < 2 ^ (prefixWord ++ tailWord_473275).sum := by decide
  have hdescent : baseEnd_473275 < baseStart_473275 := by decide
  rcases family_descends (prefixWord ++ tailWord_473275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473294 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_473294 : Nat := 118140960795 + 473294 * 2 ^ 59
def prefixEnd_473294 : Nat := 4983230072969 + 3 ^ 40 * 473294 * 2
def baseEnd_473294 : Nat := 162018208592784312498911

theorem tailTrace_473294 : CollatzResearch.WordTrace tailWord_473294 prefixEnd_473294 162018208592784312498911 := by
  unfold tailWord_473294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157806293418018128116367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11508300231562763349953957 2157806293418018128116367)
  ·
    refine ⟨3236709440127027192174551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157806293418018128116367 3236709440127027192174551)
    ·
      refine ⟨4855064160190540788261827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236709440127027192174551 4855064160190540788261827)
      ·
        refine ⟨7282596240285811182392741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855064160190540788261827 7282596240285811182392741)
        ·
          refine ⟨1365486795053589596698639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7282596240285811182392741 1365486795053589596698639)
          ·
            refine ⟨2048230192580384395047959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365486795053589596698639 2048230192580384395047959)
            ·
              refine ⟨3072345288870576592571939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048230192580384395047959 3072345288870576592571939)
              ·
                refine ⟨4608517933305864888857909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072345288870576592571939 4608517933305864888857909)
                ·
                  refine ⟨432048556247424833330429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608517933305864888857909 432048556247424833330429)
                  ·
                    refine ⟨162018208592784312498911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432048556247424833330429 162018208592784312498911)
                    ·
                      rfl

theorem cell22_473294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_473294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473294 prefixEnd_473294 := by exact prefixLift 473294
  have htrace : WordTrace (prefixWord ++ tailWord_473294) baseStart_473294 baseEnd_473294 := by
    simpa [prefixWord, tailWord_473294, baseEnd_473294] using wordTrace_append hprefix tailTrace_473294
  have hstable : (prefixWord ++ tailWord_473294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473294).length < 2 ^ (prefixWord ++ tailWord_473294).sum := by decide
  have hdescent : baseEnd_473294 < baseStart_473294 := by decide
  rcases family_descends (prefixWord ++ tailWord_473294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473322 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_473322 : Nat := 118140960795 + 473322 * 2 ^ 59
def prefixEnd_473322 : Nat := 4983230072969 + 3 ^ 40 * 473322 * 2
def baseEnd_473322 : Nat := 162027793565001572798825

theorem tailTrace_473322 : CollatzResearch.WordTrace tailWord_473322 prefixEnd_473322 162027793565001572798825 := by
  unfold tailWord_473322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315867897810676451737555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11508981060828470537966813 4315867897810676451737555)
  ·
    refine ⟨6473801846716014677606333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315867897810676451737555 6473801846716014677606333)
    ·
      refine ⟨2427675692518505504102375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6473801846716014677606333 2427675692518505504102375)
      ·
        refine ⟨3641513538777758256153563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427675692518505504102375 3641513538777758256153563)
        ·
          refine ⟨5462270308166637384230345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641513538777758256153563 5462270308166637384230345)
          ·
            refine ⟨4096702731124978038172759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5462270308166637384230345 4096702731124978038172759)
            ·
              refine ⟨6145054096687467057259139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096702731124978038172759 6145054096687467057259139)
              ·
                refine ⟨9217581145031200585888709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145054096687467057259139 9217581145031200585888709)
                ·
                  refine ⟨1728296464693350109854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9217581145031200585888709 1728296464693350109854133)
                  ·
                    refine ⟨162027793565001572798825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1728296464693350109854133 162027793565001572798825)
                    ·
                      rfl

theorem cell22_473322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_473322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473322 prefixEnd_473322 := by exact prefixLift 473322
  have htrace : WordTrace (prefixWord ++ tailWord_473322) baseStart_473322 baseEnd_473322 := by
    simpa [prefixWord, tailWord_473322, baseEnd_473322] using wordTrace_append hprefix tailTrace_473322
  have hstable : (prefixWord ++ tailWord_473322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473322).length < 2 ^ (prefixWord ++ tailWord_473322).sum := by decide
  have hdescent : baseEnd_473322 < baseStart_473322 := by decide
  rcases family_descends (prefixWord ++ tailWord_473322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473337 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_473337 : Nat := 118140960795 + 473337 * 2 ^ 59
def prefixEnd_473337 : Nat := 4983230072969 + 3 ^ 40 * 473337 * 2
def baseEnd_473337 : Nat := 162032928371546533673779

theorem tailTrace_473337 : CollatzResearch.WordTrace tailWord_473337 prefixEnd_473337 162032928371546533673779 := by
  unfold tailWord_473337
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264018686188363368746265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11509345790792242245830843 17264018686188363368746265)
  ·
    refine ⟨12948014014641272526559699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17264018686188363368746265 12948014014641272526559699)
    ·
      refine ⟨19422021021961908789839549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12948014014641272526559699 19422021021961908789839549)
      ·
        refine ⟨7283257883235715796189831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19422021021961908789839549 7283257883235715796189831)
        ·
          refine ⟨10924886824853573694284747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283257883235715796189831 10924886824853573694284747)
          ·
            refine ⟨16387330237280360541427121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924886824853573694284747 16387330237280360541427121)
            ·
              refine ⟨12290497677960270406070341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16387330237280360541427121 12290497677960270406070341)
              ·
                refine ⟨2304468314617550701138189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12290497677960270406070341 2304468314617550701138189)
                ·
                  refine ⟨864175617981581512926821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2304468314617550701138189 864175617981581512926821)
                  ·
                    refine ⟨162032928371546533673779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864175617981581512926821 162032928371546533673779)
                    ·
                      rfl

theorem cell22_473337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_473337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473337 prefixEnd_473337 := by exact prefixLift 473337
  have htrace : WordTrace (prefixWord ++ tailWord_473337) baseStart_473337 baseEnd_473337 := by
    simpa [prefixWord, tailWord_473337, baseEnd_473337] using wordTrace_append hprefix tailTrace_473337
  have hstable : (prefixWord ++ tailWord_473337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473337).length < 2 ^ (prefixWord ++ tailWord_473337).sum := by decide
  have hdescent : baseEnd_473337 < baseStart_473337 := by decide
  rcases family_descends (prefixWord ++ tailWord_473337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473354 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_473354 : Nat := 118140960795 + 473354 * 2 ^ 59
def prefixEnd_473354 : Nat := 4983230072969 + 3 ^ 40 * 473354 * 2
def baseEnd_473354 : Nat := 162038747818964155998727

theorem tailTrace_473354 : CollatzResearch.WordTrace tailWord_473354 prefixEnd_473354 162038747818964155998727 := by
  unfold tailWord_473354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316159681781693818028779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11509759151417850181410077 4316159681781693818028779)
  ·
    refine ⟨6474239522672540727043169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4316159681781693818028779 6474239522672540727043169)
    ·
      refine ⟨4855679642004405545282377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6474239522672540727043169 4855679642004405545282377)
      ·
        refine ⟨3641759731503304158961783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4855679642004405545282377 3641759731503304158961783)
        ·
          refine ⟨5462639597254956238442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641759731503304158961783 5462639597254956238442675)
          ·
            refine ⟨8193959395882434357664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462639597254956238442675 8193959395882434357664013)
            ·
              refine ⟨3072734773455912884124005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8193959395882434357664013 3072734773455912884124005)
              ·
                refine ⟨576137770022983665773251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3072734773455912884124005 576137770022983665773251)
                ·
                  refine ⟨864206655034475498659877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576137770022983665773251 864206655034475498659877)
                  ·
                    refine ⟨162038747818964155998727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864206655034475498659877 162038747818964155998727)
                    ·
                      rfl

theorem cell22_473354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_473354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473354 prefixEnd_473354 := by exact prefixLift 473354
  have htrace : WordTrace (prefixWord ++ tailWord_473354) baseStart_473354 baseEnd_473354 := by
    simpa [prefixWord, tailWord_473354, baseEnd_473354] using wordTrace_append hprefix tailTrace_473354
  have hstable : (prefixWord ++ tailWord_473354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473354).length < 2 ^ (prefixWord ++ tailWord_473354).sum := by decide
  have hdescent : baseEnd_473354 < baseStart_473354 := by decide
  rcases family_descends (prefixWord ++ tailWord_473354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473504 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_473504 : Nat := 118140960795 + 473504 * 2 ^ 59
def prefixEnd_473504 : Nat := 4983230072969 + 3 ^ 40 * 473504 * 2
def baseEnd_473504 : Nat := 54030031961471254916089

theorem tailTrace_473504 : CollatzResearch.WordTrace tailWord_473504 prefixEnd_473504 54030031961471254916089 := by
  unfold tailWord_473504
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635054838291675445037783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11513406451055567260050377 8635054838291675445037783)
  ·
    refine ⟨12952582257437513167556675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635054838291675445037783 12952582257437513167556675)
    ·
      refine ⟨19428873386156269751335013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12952582257437513167556675 19428873386156269751335013)
      ·
        refine ⟨3642913759904300578375315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19428873386156269751335013 3642913759904300578375315)
        ·
          refine ⟨5464370639856450867562973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642913759904300578375315 5464370639856450867562973)
          ·
            refine ⟨2049138989946169075336115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5464370639856450867562973 2049138989946169075336115)
            ·
              refine ⟨3073708484919253613004173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049138989946169075336115 3073708484919253613004173)
              ·
                refine ⟨1152640681844720104876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3073708484919253613004173 1152640681844720104876565)
                ·
                  refine ⟨54030031961471254916089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1152640681844720104876565 54030031961471254916089)
                  ·
                    rfl

theorem cell22_473504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_473504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473504 prefixEnd_473504 := by exact prefixLift 473504
  have htrace : WordTrace (prefixWord ++ tailWord_473504) baseStart_473504 baseEnd_473504 := by
    simpa [prefixWord, tailWord_473504, baseEnd_473504] using wordTrace_append hprefix tailTrace_473504
  have hstable : (prefixWord ++ tailWord_473504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473504).length < 2 ^ (prefixWord ++ tailWord_473504).sum := by decide
  have hdescent : baseEnd_473504 < baseStart_473504 := by decide
  rcases family_descends (prefixWord ++ tailWord_473504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473594 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_473594 : Nat := 118140960795 + 473594 * 2 ^ 59
def prefixEnd_473594 : Nat := 4983230072969 + 3 ^ 40 * 473594 * 2
def baseEnd_473594 : Nat := 54040301574561176665997

theorem tailTrace_473594 : CollatzResearch.WordTrace tailWord_473594 prefixEnd_473594 54040301574561176665997 := by
  unfold tailWord_473594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318348061564324065212959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11515594830838197507234557 4318348061564324065212959)
  ·
    refine ⟨6477522092346486097819439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318348061564324065212959 6477522092346486097819439)
    ·
      refine ⟨9716283138519729146729159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6477522092346486097819439 9716283138519729146729159)
      ·
        refine ⟨14574424707779593720093739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716283138519729146729159 14574424707779593720093739)
        ·
          refine ⟨21861637061669390580140609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574424707779593720093739 21861637061669390580140609)
          ·
            refine ⟨16396227796252042935105457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21861637061669390580140609 16396227796252042935105457)
            ·
              refine ⟨12297170847189032201329093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16396227796252042935105457 12297170847189032201329093)
              ·
                refine ⟨2305719533847943537749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12297170847189032201329093 2305719533847943537749205)
                ·
                  refine ⟨54040301574561176665997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2305719533847943537749205 54040301574561176665997)
                  ·
                    rfl

theorem cell22_473594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_473594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473594 prefixEnd_473594 := by exact prefixLift 473594
  have htrace : WordTrace (prefixWord ++ tailWord_473594) baseStart_473594 baseEnd_473594 := by
    simpa [prefixWord, tailWord_473594, baseEnd_473594] using wordTrace_append hprefix tailTrace_473594
  have hstable : (prefixWord ++ tailWord_473594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473594).length < 2 ^ (prefixWord ++ tailWord_473594).sum := by decide
  have hdescent : baseEnd_473594 < baseStart_473594 := by decide
  rcases family_descends (prefixWord ++ tailWord_473594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473606 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_473606 : Nat := 118140960795 + 473606 * 2 ^ 59
def prefixEnd_473606 : Nat := 4983230072969 + 3 ^ 40 * 473606 * 2
def baseEnd_473606 : Nat := 54041670856306499565985

theorem tailTrace_473606 : CollatzResearch.WordTrace tailWord_473606 prefixEnd_473606 54041670856306499565985 := by
  unfold tailWord_473606
  simp only [CollatzResearch.WordTrace]
  refine ⟨539807185069181947196521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11515886614809214873525781 539807185069181947196521)
  ·
    refine ⟨404855388801886460397391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 539807185069181947196521 404855388801886460397391)
    ·
      refine ⟨607283083202829690596087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404855388801886460397391 607283083202829690596087)
      ·
        refine ⟨910924624804244535894131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607283083202829690596087 910924624804244535894131)
        ·
          refine ⟨1366386937206366803841197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910924624804244535894131 1366386937206366803841197)
          ·
            refine ⟨512395101452387551440449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366386937206366803841197 512395101452387551440449)
            ·
              refine ⟨384296326089290663580337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512395101452387551440449 384296326089290663580337)
              ·
                refine ⟨288222244566967997685253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384296326089290663580337 288222244566967997685253)
                ·
                  refine ⟨54041670856306499565985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288222244566967997685253 54041670856306499565985)
                  ·
                    rfl

theorem cell22_473606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_473606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473606 prefixEnd_473606 := by exact prefixLift 473606
  have htrace : WordTrace (prefixWord ++ tailWord_473606) baseStart_473606 baseEnd_473606 := by
    simpa [prefixWord, tailWord_473606, baseEnd_473606] using wordTrace_append hprefix tailTrace_473606
  have hstable : (prefixWord ++ tailWord_473606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473606).length < 2 ^ (prefixWord ++ tailWord_473606).sum := by decide
  have hdescent : baseEnd_473606 < baseStart_473606 := by decide
  rcases family_descends (prefixWord ++ tailWord_473606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473611 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 5]
def baseStart_473611 : Nat := 118140960795 + 473611 * 2 ^ 59
def prefixEnd_473611 : Nat := 4983230072969 + 3 ^ 40 * 473611 * 2
def baseEnd_473611 : Nat := 54042241390367050774313

theorem tailTrace_473611 : CollatzResearch.WordTrace tailWord_473611 prefixEnd_473611 54042241390367050774313 := by
  unfold tailWord_473611
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274012287195708164220687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11516008191463805442813791 17274012287195708164220687)
  ·
    refine ⟨25911018430793562246331031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17274012287195708164220687 25911018430793562246331031)
    ·
      refine ⟨38866527646190343369496547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25911018430793562246331031 38866527646190343369496547)
      ·
        refine ⟨58299791469285515054244821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38866527646190343369496547 58299791469285515054244821)
        ·
          refine ⟨1366401362561379259083863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58299791469285515054244821 1366401362561379259083863)
          ·
            refine ⟨2049602043842068888625795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366401362561379259083863 2049602043842068888625795)
            ·
              refine ⟨3074403065763103332938693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049602043842068888625795 3074403065763103332938693)
              ·
                refine ⟨576450574830581874926005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3074403065763103332938693 576450574830581874926005)
                ·
                  refine ⟨54042241390367050774313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576450574830581874926005 54042241390367050774313)
                  ·
                    rfl

theorem cell22_473611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].length) (baseStart_473611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473611 prefixEnd_473611 := by exact prefixLift 473611
  have htrace : WordTrace (prefixWord ++ tailWord_473611) baseStart_473611 baseEnd_473611 := by
    simpa [prefixWord, tailWord_473611, baseEnd_473611] using wordTrace_append hprefix tailTrace_473611
  have hstable : (prefixWord ++ tailWord_473611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473611).length < 2 ^ (prefixWord ++ tailWord_473611).sum := by decide
  have hdescent : baseEnd_473611 < baseStart_473611 := by decide
  rcases family_descends (prefixWord ++ tailWord_473611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473658 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_473658 : Nat := 118140960795 + 473658 * 2 ^ 59
def prefixEnd_473658 : Nat := 4983230072969 + 3 ^ 40 * 473658 * 2
def baseEnd_473658 : Nat := 162142813231608696397795

theorem tailTrace_473658 : CollatzResearch.WordTrace tailWord_473658 prefixEnd_473658 162142813231608696397795 := by
  unfold tailWord_473658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318931629506358797795407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11517151012016956794121085 4318931629506358797795407)
  ·
    refine ⟨6478397444259538196693111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318931629506358797795407 6478397444259538196693111)
    ·
      refine ⟨9717596166389307295039667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478397444259538196693111 9717596166389307295039667)
      ·
        refine ⟨14576394249583960942559501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717596166389307295039667 14576394249583960942559501)
        ·
          refine ⟨5466147843593985353459813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14576394249583960942559501 5466147843593985353459813)
          ·
            refine ⟨1024902720673872253773715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5466147843593985353459813 1024902720673872253773715)
            ·
              refine ⟨1537354081010808380660573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024902720673872253773715 1537354081010808380660573)
              ·
                refine ⟨576507780379053142747715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537354081010808380660573 576507780379053142747715)
                ·
                  refine ⟨864761670568579714121573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576507780379053142747715 864761670568579714121573)
                  ·
                    refine ⟨162142813231608696397795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864761670568579714121573 162142813231608696397795)
                    ·
                      rfl

theorem cell22_473658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_473658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473658 prefixEnd_473658 := by exact prefixLift 473658
  have htrace : WordTrace (prefixWord ++ tailWord_473658) baseStart_473658 baseEnd_473658 := by
    simpa [prefixWord, tailWord_473658, baseEnd_473658] using wordTrace_append hprefix tailTrace_473658
  have hstable : (prefixWord ++ tailWord_473658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473658).length < 2 ^ (prefixWord ++ tailWord_473658).sum := by decide
  have hdescent : baseEnd_473658 < baseStart_473658 := by decide
  rcases family_descends (prefixWord ++ tailWord_473658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473662 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_473662 : Nat := 118140960795 + 473662 * 2 ^ 59
def prefixEnd_473662 : Nat := 4983230072969 + 3 ^ 40 * 473662 * 2
def baseEnd_473662 : Nat := 54048060837784673099261

theorem tailTrace_473662 : CollatzResearch.WordTrace tailWord_473662 prefixEnd_473662 54048060837784673099261 := by
  unfold tailWord_473662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159484051251367984290905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11517248273340629249551493 2159484051251367984290905)
  ·
    refine ⟨1619613038438525988218179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2159484051251367984290905 1619613038438525988218179)
    ·
      refine ⟨2429419557657788982327269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619613038438525988218179 2429419557657788982327269)
      ·
        refine ⟨455516167060835434186363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2429419557657788982327269 455516167060835434186363)
        ·
          refine ⟨683274250591253151279545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455516167060835434186363 683274250591253151279545)
          ·
            refine ⟨512455687943439863459659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683274250591253151279545 512455687943439863459659)
            ·
              refine ⟨768683531915159795189489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512455687943439863459659 768683531915159795189489)
              ·
                refine ⟨576512648936369846392117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768683531915159795189489 576512648936369846392117)
                ·
                  refine ⟨54048060837784673099261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576512648936369846392117 54048060837784673099261)
                  ·
                    rfl

theorem cell22_473662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_473662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473662 prefixEnd_473662 := by exact prefixLift 473662
  have htrace : WordTrace (prefixWord ++ tailWord_473662) baseStart_473662 baseEnd_473662 := by
    simpa [prefixWord, tailWord_473662, baseEnd_473662] using wordTrace_append hprefix tailTrace_473662
  have hstable : (prefixWord ++ tailWord_473662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473662).length < 2 ^ (prefixWord ++ tailWord_473662).sum := by decide
  have hdescent : baseEnd_473662 < baseStart_473662 := by decide
  rcases family_descends (prefixWord ++ tailWord_473662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473688 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_473688 : Nat := 118140960795 + 473688 * 2 ^ 59
def prefixEnd_473688 : Nat := 4983230072969 + 3 ^ 40 * 473688 * 2
def baseEnd_473688 : Nat := 162153082844698618147703

theorem tailTrace_473688 : CollatzResearch.WordTrace tailWord_473688 prefixEnd_473688 162153082844698618147703 := by
  unfold tailWord_473688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638410353958375157386859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11517880471944500209849145 8638410353958375157386859)
  ·
    refine ⟨12957615530937562736080289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8638410353958375157386859 12957615530937562736080289)
    ·
      refine ⟨9718211648203172052060217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12957615530937562736080289 9718211648203172052060217)
      ·
        refine ⟨7288658736152379039045163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9718211648203172052060217 7288658736152379039045163)
        ·
          refine ⟨10932988104228568558567745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288658736152379039045163 10932988104228568558567745)
          ·
            refine ⟨8199741078171426418925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10932988104228568558567745 8199741078171426418925809)
            ·
              refine ⟨6149805808628569814194357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8199741078171426418925809 6149805808628569814194357)
              ·
                refine ⟨576544294558928420080721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6149805808628569814194357 576544294558928420080721)
                ·
                  refine ⟨432408220919196315060541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576544294558928420080721 432408220919196315060541)
                  ·
                    refine ⟨162153082844698618147703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432408220919196315060541 162153082844698618147703)
                    ·
                      rfl

theorem cell22_473688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_473688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473688 prefixEnd_473688 := by exact prefixLift 473688
  have htrace : WordTrace (prefixWord ++ tailWord_473688) baseStart_473688 baseEnd_473688 := by
    simpa [prefixWord, tailWord_473688, baseEnd_473688] using wordTrace_append hprefix tailTrace_473688
  have hstable : (prefixWord ++ tailWord_473688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473688).length < 2 ^ (prefixWord ++ tailWord_473688).sum := by decide
  have hdescent : baseEnd_473688 < baseStart_473688 := by decide
  rcases family_descends (prefixWord ++ tailWord_473688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473823 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_473823 : Nat := 118140960795 + 473823 * 2 ^ 59
def prefixEnd_473823 : Nat := 4983230072969 + 3 ^ 40 * 473823 * 2
def baseEnd_473823 : Nat := 162199296103603266022289

theorem tailTrace_473823 : CollatzResearch.WordTrace tailWord_473823 prefixEnd_473823 162199296103603266022289 := by
  unfold tailWord_473823
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281744562427668370938123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521163041618445580625415 17281744562427668370938123)
  ·
    refine ⟨25922616843641502556407185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17281744562427668370938123 25922616843641502556407185)
    ·
      refine ⟨19441962632731126917305389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25922616843641502556407185 19441962632731126917305389)
      ·
        refine ⟨7290735987274172593989521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19441962632731126917305389 7290735987274172593989521)
        ·
          refine ⟨5468051990455629445492141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290735987274172593989521 5468051990455629445492141)
          ·
            refine ⟨2050519496420861042059553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5468051990455629445492141 2050519496420861042059553)
            ·
              refine ⟨1537889622315645781544665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050519496420861042059553 1537889622315645781544665)
              ·
                refine ⟨1153417216736734336158499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537889622315645781544665 1153417216736734336158499)
                ·
                  refine ⟨1730125825105101504237749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153417216736734336158499 1730125825105101504237749)
                  ·
                    refine ⟨162199296103603266022289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1730125825105101504237749 162199296103603266022289)
                    ·
                      rfl

theorem cell22_473823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_473823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473823 prefixEnd_473823 := by exact prefixLift 473823
  have htrace : WordTrace (prefixWord ++ tailWord_473823) baseStart_473823 baseEnd_473823 := by
    simpa [prefixWord, tailWord_473823, baseEnd_473823] using wordTrace_append hprefix tailTrace_473823
  have hstable : (prefixWord ++ tailWord_473823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473823).length < 2 ^ (prefixWord ++ tailWord_473823).sum := by decide
  have hdescent : baseEnd_473823 < baseStart_473823 := by decide
  rcases family_descends (prefixWord ++ tailWord_473823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473825 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 4]
def baseStart_473825 : Nat := 118140960795 + 473825 * 2 ^ 59
def prefixEnd_473825 : Nat := 4983230072969 + 3 ^ 40 * 473825 * 2
def baseEnd_473825 : Nat := 54066660248158642490761

theorem tailTrace_473825 : CollatzResearch.WordTrace tailWord_473825 prefixEnd_473825 54066660248158642490761 := by
  unfold tailWord_473825
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281817508420422712510929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521211672280281808340619 17281817508420422712510929)
  ·
    refine ⟨12961363131315317034383197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17281817508420422712510929 12961363131315317034383197)
    ·
      refine ⟨4860511174243243887893699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12961363131315317034383197 4860511174243243887893699)
      ·
        refine ⟨7290766761364865831840549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860511174243243887893699 7290766761364865831840549)
        ·
          refine ⟨1367018767755912343470103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7290766761364865831840549 1367018767755912343470103)
          ·
            refine ⟨2050528151633868515205155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367018767755912343470103 2050528151633868515205155)
            ·
              refine ⟨3075792227450802772807733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050528151633868515205155 3075792227450802772807733)
              ·
                refine ⟨288355521323512759950725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3075792227450802772807733 288355521323512759950725)
                ·
                  refine ⟨54066660248158642490761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288355521323512759950725 54066660248158642490761)
                  ·
                    rfl

theorem cell22_473825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_473825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473825 prefixEnd_473825 := by exact prefixLift 473825
  have htrace : WordTrace (prefixWord ++ tailWord_473825) baseStart_473825 baseEnd_473825 := by
    simpa [prefixWord, tailWord_473825, baseEnd_473825] using wordTrace_append hprefix tailTrace_473825
  have hstable : (prefixWord ++ tailWord_473825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473825).length < 2 ^ (prefixWord ++ tailWord_473825).sum := by decide
  have hdescent : baseEnd_473825 < baseStart_473825 := by decide
  rcases family_descends (prefixWord ++ tailWord_473825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473827 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 1, 4]
def baseStart_473827 : Nat := 118140960795 + 473827 * 2 ^ 59
def prefixEnd_473827 : Nat := 4983230072969 + 3 ^ 40 * 473827 * 2
def baseEnd_473827 : Nat := 162200665385348588922277

theorem tailTrace_473827 : CollatzResearch.WordTrace tailWord_473827 prefixEnd_473827 162200665385348588922277 := by
  unfold tailWord_473827
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281890454413177054083735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521260302942118036055823 17281890454413177054083735)
  ·
    refine ⟨25922835681619765581125603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17281890454413177054083735 25922835681619765581125603)
    ·
      refine ⟨38884253522429648371688405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25922835681619765581125603 38884253522429648371688405)
      ·
        refine ⟨911349691931944883711447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 38884253522429648371688405 911349691931944883711447)
        ·
          refine ⟨1367024537897917325567171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911349691931944883711447 1367024537897917325567171)
          ·
            refine ⟨2050536806846875988350757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367024537897917325567171 2050536806846875988350757)
            ·
              refine ⟨384475651283789247815767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2050536806846875988350757 384475651283789247815767)
              ·
                refine ⟨576713476925683871723651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384475651283789247815767 576713476925683871723651)
                ·
                  refine ⟨865070215388525807585477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576713476925683871723651 865070215388525807585477)
                  ·
                    refine ⟨162200665385348588922277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865070215388525807585477 162200665385348588922277)
                    ·
                      rfl

theorem cell22_473827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 4].length) (baseStart_473827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473827 prefixEnd_473827 := by exact prefixLift 473827
  have htrace : WordTrace (prefixWord ++ tailWord_473827) baseStart_473827 baseEnd_473827 := by
    simpa [prefixWord, tailWord_473827, baseEnd_473827] using wordTrace_append hprefix tailTrace_473827
  have hstable : (prefixWord ++ tailWord_473827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473827).length < 2 ^ (prefixWord ++ tailWord_473827).sum := by decide
  have hdescent : baseEnd_473827 < baseStart_473827 := by decide
  rcases family_descends (prefixWord ++ tailWord_473827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473908 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_473908 : Nat := 118140960795 + 473908 * 2 ^ 59
def prefixEnd_473908 : Nat := 4983230072969 + 3 ^ 40 * 473908 * 2
def baseEnd_473908 : Nat := 162228393340691377647029

theorem tailTrace_473908 : CollatzResearch.WordTrace tailWord_473908 prefixEnd_473908 162228393340691377647029 := by
  unfold tailWord_473908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642422383559863943891189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11523229844746485258521585 8642422383559863943891189)
  ·
    refine ⟨810227098458737244739799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8642422383559863943891189 810227098458737244739799)
    ·
      refine ⟨1215340647688105867109699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810227098458737244739799 1215340647688105867109699)
      ·
        refine ⟨1823010971532158800664549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215340647688105867109699 1823010971532158800664549)
        ·
          refine ⟨341814557162279775124603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1823010971532158800664549 341814557162279775124603)
          ·
            refine ⟨512721835743419662686905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341814557162279775124603 512721835743419662686905)
            ·
              refine ⟨384541376807564747015179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512721835743419662686905 384541376807564747015179)
              ·
                refine ⟨576812065211347120522769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384541376807564747015179 576812065211347120522769)
                ·
                  refine ⟨432609048908510340392077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576812065211347120522769 432609048908510340392077)
                  ·
                    refine ⟨162228393340691377647029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432609048908510340392077 162228393340691377647029)
                    ·
                      rfl

theorem cell22_473908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_473908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473908 prefixEnd_473908 := by exact prefixLift 473908
  have htrace : WordTrace (prefixWord ++ tailWord_473908) baseStart_473908 baseEnd_473908 := by
    simpa [prefixWord, tailWord_473908, baseEnd_473908] using wordTrace_append hprefix tailTrace_473908
  have hstable : (prefixWord ++ tailWord_473908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473908).length < 2 ^ (prefixWord ++ tailWord_473908).sum := by decide
  have hdescent : baseEnd_473908 < baseStart_473908 := by decide
  rcases family_descends (prefixWord ++ tailWord_473908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473994 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_473994 : Nat := 118140960795 + 473994 * 2 ^ 59
def prefixEnd_473994 : Nat := 4983230072969 + 3 ^ 40 * 473994 * 2
def baseEnd_473994 : Nat := 54085944299405273332255

theorem tailTrace_473994 : CollatzResearch.WordTrace tailWord_473994 prefixEnd_473994 54085944299405273332255 := by
  unfold tailWord_473994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321995361202041143853259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11525320963205443050275357 4321995361202041143853259)
  ·
    refine ⟨6482993041803061715779889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321995361202041143853259 6482993041803061715779889)
    ·
      refine ⟨4862244781352296286834917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6482993041803061715779889 4862244781352296286834917)
      ·
        refine ⟨911670896503555553781547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4862244781352296286834917 911670896503555553781547)
        ·
          refine ⟨1367506344755333330672321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911670896503555553781547 1367506344755333330672321)
          ·
            refine ⟨1025629758566499998004241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367506344755333330672321 1025629758566499998004241)
            ·
              refine ⟨769222318924874998503181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025629758566499998004241 769222318924874998503181)
              ·
                refine ⟨288458369596828124438693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769222318924874998503181 288458369596828124438693)
                ·
                  refine ⟨54085944299405273332255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288458369596828124438693 54085944299405273332255)
                  ·
                    rfl

theorem cell22_473994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_473994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_473994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_473994 prefixEnd_473994 := by exact prefixLift 473994
  have htrace : WordTrace (prefixWord ++ tailWord_473994) baseStart_473994 baseEnd_473994 := by
    simpa [prefixWord, tailWord_473994, baseEnd_473994] using wordTrace_append hprefix tailTrace_473994
  have hstable : (prefixWord ++ tailWord_473994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473994).length < 2 ^ (prefixWord ++ tailWord_473994).sum := by decide
  have hdescent : baseEnd_473994 < baseStart_473994 := by decide
  rcases family_descends (prefixWord ++ tailWord_473994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474037 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_474037 : Nat := 118140960795 + 474037 * 2 ^ 59
def prefixEnd_474037 : Nat := 4983230072969 + 3 ^ 40 * 474037 * 2
def baseEnd_474037 : Nat := 162272552676978041171633

theorem tailTrace_474037 : CollatzResearch.WordTrace tailWord_474037 prefixEnd_474037 162272552676978041171633 := by
  unfold tailWord_474037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17289549783652382919228365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11526366522434921946152243 17289549783652382919228365)
  ·
    refine ⟨6483581168869643594710637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17289549783652382919228365 6483581168869643594710637)
    ·
      refine ⟨2431342938326116348016489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6483581168869643594710637 2431342938326116348016489)
      ·
        refine ⟨1823507203744587261012367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431342938326116348016489 1823507203744587261012367)
        ·
          refine ⟨2735260805616880891518551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823507203744587261012367 2735260805616880891518551)
          ·
            refine ⟨4102891208425321337277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735260805616880891518551 4102891208425321337277827)
            ·
              refine ⟨6154336812637982005916741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102891208425321337277827 6154336812637982005916741)
              ·
                refine ⟨1153938152369621626109389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6154336812637982005916741 1153938152369621626109389)
                ·
                  refine ⟨432726807138608109791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153938152369621626109389 432726807138608109791021)
                  ·
                    refine ⟨162272552676978041171633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432726807138608109791021 162272552676978041171633)
                    ·
                      rfl

theorem cell22_474037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_474037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474037 prefixEnd_474037 := by exact prefixLift 474037
  have htrace : WordTrace (prefixWord ++ tailWord_474037) baseStart_474037 baseEnd_474037 := by
    simpa [prefixWord, tailWord_474037, baseEnd_474037] using wordTrace_append hprefix tailTrace_474037
  have hstable : (prefixWord ++ tailWord_474037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474037).length < 2 ^ (prefixWord ++ tailWord_474037).sum := by decide
  have hdescent : baseEnd_474037 < baseStart_474037 := by decide
  rcases family_descends (prefixWord ++ tailWord_474037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474097 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_474097 : Nat := 118140960795 + 474097 * 2 ^ 59
def prefixEnd_474097 : Nat := 4983230072969 + 3 ^ 40 * 474097 * 2
def baseEnd_474097 : Nat := 162293091903157884671449

theorem tailTrace_474097 : CollatzResearch.WordTrace tailWord_474097 prefixEnd_474097 162293091903157884671449 := by
  unfold tailWord_474097
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291738163435013166412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11527825442290008777608363 17291738163435013166412545)
  ·
    refine ⟨12968803622576259874809409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17291738163435013166412545 12968803622576259874809409)
    ·
      refine ⟨9726602716932194906107057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12968803622576259874809409 9726602716932194906107057)
      ·
        refine ⟨7294952037699146179580293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9726602716932194906107057 7294952037699146179580293)
        ·
          refine ⟨1367803507068589908671305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7294952037699146179580293 1367803507068589908671305)
          ·
            refine ⟨1025852630301442431503479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367803507068589908671305 1025852630301442431503479)
            ·
              refine ⟨1538778945452163647255219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025852630301442431503479 1538778945452163647255219)
              ·
                refine ⟨2308168418178245470882829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538778945452163647255219 2308168418178245470882829)
                ·
                  refine ⟨865563156816842051581061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2308168418178245470882829 865563156816842051581061)
                  ·
                    refine ⟨162293091903157884671449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865563156816842051581061 162293091903157884671449)
                    ·
                      rfl

theorem cell22_474097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_474097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474097 prefixEnd_474097 := by exact prefixLift 474097
  have htrace : WordTrace (prefixWord ++ tailWord_474097) baseStart_474097 baseEnd_474097 := by
    simpa [prefixWord, tailWord_474097, baseEnd_474097] using wordTrace_append hprefix tailTrace_474097
  have hstable : (prefixWord ++ tailWord_474097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474097).length < 2 ^ (prefixWord ++ tailWord_474097).sum := by decide
  have hdescent : baseEnd_474097 < baseStart_474097 := by decide
  rcases family_descends (prefixWord ++ tailWord_474097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474266 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_474266 : Nat := 118140960795 + 474266 * 2 ^ 59
def prefixEnd_474266 : Nat := 4983230072969 + 3 ^ 40 * 474266 * 2
def baseEnd_474266 : Nat := 162350944056897777195931

theorem tailTrace_474266 : CollatzResearch.WordTrace tailWord_474266 prefixEnd_474266 162350944056897777195931 := by
  unfold tailWord_474266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324475524955688757328663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11531934733215170019543101 4324475524955688757328663)
  ·
    refine ⟨6486713287433533135992995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324475524955688757328663 6486713287433533135992995)
    ·
      refine ⟨9730069931150299703989493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486713287433533135992995 9730069931150299703989493)
      ·
        refine ⟨912194056045340597249015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9730069931150299703989493 912194056045340597249015)
        ·
          refine ⟨1368291084068010895873523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912194056045340597249015 1368291084068010895873523)
          ·
            refine ⟨2052436626102016343810285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368291084068010895873523 2052436626102016343810285)
            ·
              refine ⟨769663734788256128928857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052436626102016343810285 769663734788256128928857)
              ·
                refine ⟨577247801091192096696643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769663734788256128928857 577247801091192096696643)
                ·
                  refine ⟨865871701636788145044965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577247801091192096696643 865871701636788145044965)
                  ·
                    refine ⟨162350944056897777195931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865871701636788145044965 162350944056897777195931)
                    ·
                      rfl

theorem cell22_474266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_474266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474266 prefixEnd_474266 := by exact prefixLift 474266
  have htrace : WordTrace (prefixWord ++ tailWord_474266) baseStart_474266 baseEnd_474266 := by
    simpa [prefixWord, tailWord_474266, baseEnd_474266] using wordTrace_append hprefix tailTrace_474266
  have hstable : (prefixWord ++ tailWord_474266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474266).length < 2 ^ (prefixWord ++ tailWord_474266).sum := by decide
  have hdescent : baseEnd_474266 < baseStart_474266 := by decide
  rcases family_descends (prefixWord ++ tailWord_474266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474279 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_474279 : Nat := 118140960795 + 474279 * 2 ^ 59
def prefixEnd_474279 : Nat := 4983230072969 + 3 ^ 40 * 474279 * 2
def baseEnd_474279 : Nat := 162355394222570076620891

theorem tailTrace_474279 : CollatzResearch.WordTrace tailWord_474279 prefixEnd_474279 162355394222570076620891 := by
  unfold tailWord_474279
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298376248775658249537891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11532250832517105499691927 17298376248775658249537891)
  ·
    refine ⟨25947564373163487374306837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17298376248775658249537891 25947564373163487374306837)
    ·
      refine ⟨1216292079992038470670633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25947564373163487374306837 1216292079992038470670633)
      ·
        refine ⟨912219059994028853002975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216292079992038470670633 912219059994028853002975)
        ·
          refine ⟨1368328589991043279504463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912219059994028853002975 1368328589991043279504463)
          ·
            refine ⟨2052492884986564919256695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368328589991043279504463 2052492884986564919256695)
            ·
              refine ⟨3078739327479847378885043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052492884986564919256695 3078739327479847378885043)
              ·
                refine ⟨4618108991219771068327565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078739327479847378885043 4618108991219771068327565)
                ·
                  refine ⟨1731790871707414150622837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4618108991219771068327565 1731790871707414150622837)
                  ·
                    refine ⟨162355394222570076620891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1731790871707414150622837 162355394222570076620891)
                    ·
                      rfl

theorem cell22_474279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_474279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474279 prefixEnd_474279 := by exact prefixLift 474279
  have htrace : WordTrace (prefixWord ++ tailWord_474279) baseStart_474279 baseEnd_474279 := by
    simpa [prefixWord, tailWord_474279, baseEnd_474279] using wordTrace_append hprefix tailTrace_474279
  have hstable : (prefixWord ++ tailWord_474279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474279).length < 2 ^ (prefixWord ++ tailWord_474279).sum := by decide
  have hdescent : baseEnd_474279 < baseStart_474279 := by decide
  rcases family_descends (prefixWord ++ tailWord_474279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474328 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_474328 : Nat := 118140960795 + 474328 * 2 ^ 59
def prefixEnd_474328 : Nat := 4983230072969 + 3 ^ 40 * 474328 * 2
def baseEnd_474328 : Nat := 162372167923950282145741

theorem tailTrace_474328 : CollatzResearch.WordTrace tailWord_474328 prefixEnd_474328 162372167923950282145741 := by
  unfold tailWord_474328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650081712799069809035819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11533442283732093078714425 8650081712799069809035819)
  ·
    refine ⟨12975122569198604713553729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650081712799069809035819 12975122569198604713553729)
    ·
      refine ⟨9731341926898953535165297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12975122569198604713553729 9731341926898953535165297)
      ·
        refine ⟨7298506445174215151373973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9731341926898953535165297 7298506445174215151373973)
        ·
          refine ⟨342117489617541335220655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7298506445174215151373973 342117489617541335220655)
          ·
            refine ⟨513176234426312002830983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342117489617541335220655 513176234426312002830983)
            ·
              refine ⟨769764351639468004246475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513176234426312002830983 769764351639468004246475)
              ·
                refine ⟨1154646527459202006369713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769764351639468004246475 1154646527459202006369713)
                ·
                  refine ⟨865984895594401504777285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154646527459202006369713 865984895594401504777285)
                  ·
                    refine ⟨162372167923950282145741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865984895594401504777285 162372167923950282145741)
                    ·
                      rfl

theorem cell22_474328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_474328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474328 prefixEnd_474328 := by exact prefixLift 474328
  have htrace : WordTrace (prefixWord ++ tailWord_474328) baseStart_474328 baseEnd_474328 := by
    simpa [prefixWord, tailWord_474328, baseEnd_474328] using wordTrace_append hprefix tailTrace_474328
  have hstable : (prefixWord ++ tailWord_474328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474328).length < 2 ^ (prefixWord ++ tailWord_474328).sum := by decide
  have hdescent : baseEnd_474328 < baseStart_474328 := by decide
  rcases family_descends (prefixWord ++ tailWord_474328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474369 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_474369 : Nat := 118140960795 + 474369 * 2 ^ 59
def prefixEnd_474369 : Nat := 4983230072969 + 3 ^ 40 * 474369 * 2
def baseEnd_474369 : Nat := 162386203061839841870615

theorem tailTrace_474369 : CollatzResearch.WordTrace tailWord_474369 prefixEnd_474369 162386203061839841870615 := by
  unfold tailWord_474369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301658818449603620314161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11534439212299735746876107 17301658818449603620314161)
  ·
    refine ⟨12976244113837202715235621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17301658818449603620314161 12976244113837202715235621)
    ·
      refine ⟨2433045771344475509106679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12976244113837202715235621 2433045771344475509106679)
      ·
        refine ⟨3649568657016713263660019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433045771344475509106679 3649568657016713263660019)
        ·
          refine ⟨5474352985525069895490029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649568657016713263660019 5474352985525069895490029)
          ·
            refine ⟨2052882369571901210808761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5474352985525069895490029 2052882369571901210808761)
            ·
              refine ⟨1539661777178925908106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052882369571901210808761 1539661777178925908106571)
              ·
                refine ⟨2309492665768388862159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539661777178925908106571 2309492665768388862159857)
                ·
                  refine ⟨1732119499326291646619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309492665768388862159857 1732119499326291646619893)
                  ·
                    refine ⟨162386203061839841870615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1732119499326291646619893 162386203061839841870615)
                    ·
                      rfl

theorem cell22_474369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_474369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474369 prefixEnd_474369 := by exact prefixLift 474369
  have htrace : WordTrace (prefixWord ++ tailWord_474369) baseStart_474369 baseEnd_474369 := by
    simpa [prefixWord, tailWord_474369, baseEnd_474369] using wordTrace_append hprefix tailTrace_474369
  have hstable : (prefixWord ++ tailWord_474369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474369).length < 2 ^ (prefixWord ++ tailWord_474369).sum := by decide
  have hdescent : baseEnd_474369 < baseStart_474369 := by decide
  rcases family_descends (prefixWord ++ tailWord_474369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474371 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 5]
def baseStart_474371 : Nat := 118140960795 + 474371 * 2 ^ 59
def prefixEnd_474371 : Nat := 4983230072969 + 3 ^ 40 * 474371 * 2
def baseEnd_474371 : Nat := 54128962567570834440203

theorem tailTrace_474371 : CollatzResearch.WordTrace tailWord_474371 prefixEnd_474371 54128962567570834440203 := by
  unfold tailWord_474371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301731764442357961886967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11534487842961571974591311 17301731764442357961886967)
  ·
    refine ⟨25952597646663536942830451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17301731764442357961886967 25952597646663536942830451)
    ·
      refine ⟨38928896469995305414245677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25952597646663536942830451 38928896469995305414245677)
      ·
        refine ⟨14598336176248239530342129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38928896469995305414245677 14598336176248239530342129)
        ·
          refine ⟨10948752132186179647756597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14598336176248239530342129 10948752132186179647756597)
          ·
            refine ⟨1026445512392454341977181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10948752132186179647756597 1026445512392454341977181)
            ·
              refine ⟨384917067147170378241443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026445512392454341977181 384917067147170378241443)
              ·
                refine ⟨577375600720755567362165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384917067147170378241443 577375600720755567362165)
                ·
                  refine ⟨54128962567570834440203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577375600720755567362165 54128962567570834440203)
                  ·
                    rfl

theorem cell22_474371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 5].length) (baseStart_474371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474371 prefixEnd_474371 := by exact prefixLift 474371
  have htrace : WordTrace (prefixWord ++ tailWord_474371) baseStart_474371 baseEnd_474371 := by
    simpa [prefixWord, tailWord_474371, baseEnd_474371] using wordTrace_append hprefix tailTrace_474371
  have hstable : (prefixWord ++ tailWord_474371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474371).length < 2 ^ (prefixWord ++ tailWord_474371).sum := by decide
  have hdescent : baseEnd_474371 < baseStart_474371 := by decide
  rcases family_descends (prefixWord ++ tailWord_474371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474422 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_474422 : Nat := 118140960795 + 474422 * 2 ^ 59
def prefixEnd_474422 : Nat := 4983230072969 + 3 ^ 40 * 474422 * 2
def baseEnd_474422 : Nat := 54134782014988456765151

theorem tailTrace_474422 : CollatzResearch.WordTrace tailWord_474422 prefixEnd_474422 54134782014988456765151 := by
  unfold tailWord_474422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081474492953599604499595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11535727924838395781329013 1081474492953599604499595)
  ·
    refine ⟨1622211739430399406749393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1081474492953599604499595 1622211739430399406749393)
    ·
      refine ⟨1216658804572799555062045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1622211739430399406749393 1216658804572799555062045)
      ·
        refine ⟨456247051714799833148267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1216658804572799555062045 456247051714799833148267)
        ·
          refine ⟨684370577572199749722401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456247051714799833148267 684370577572199749722401)
          ·
            refine ⟨513277933179149812291801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684370577572199749722401 513277933179149812291801)
            ·
              refine ⟨384958449884362359218851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513277933179149812291801 384958449884362359218851)
              ·
                refine ⟨577437674826543538828277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384958449884362359218851 577437674826543538828277)
                ·
                  refine ⟨54134782014988456765151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577437674826543538828277 54134782014988456765151)
                  ·
                    rfl

theorem cell22_474422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_474422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474422 prefixEnd_474422 := by exact prefixLift 474422
  have htrace : WordTrace (prefixWord ++ tailWord_474422) baseStart_474422 baseEnd_474422 := by
    simpa [prefixWord, tailWord_474422, baseEnd_474422] using wordTrace_append hprefix tailTrace_474422
  have hstable : (prefixWord ++ tailWord_474422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474422).length < 2 ^ (prefixWord ++ tailWord_474422).sum := by decide
  have hdescent : baseEnd_474422 < baseStart_474422 := by decide
  rcases family_descends (prefixWord ++ tailWord_474422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474444 : List Nat := [2, 2, 1, 3, 2, 2, 2, 8]
def baseStart_474444 : Nat := 118140960795 + 474444 * 2 ^ 59
def prefixEnd_474444 : Nat := 4983230072969 + 3 ^ 40 * 474444 * 2
def baseEnd_474444 : Nat := 18045764121618294027265

theorem tailTrace_474444 : CollatzResearch.WordTrace tailWord_474444 prefixEnd_474444 18045764121618294027265 := by
  unfold tailWord_474444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652197146588945714647193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11536262862118594286196257 8652197146588945714647193)
  ·
    refine ⟨6489147859941709285985395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8652197146588945714647193 6489147859941709285985395)
    ·
      refine ⟨9733721789912563928978093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489147859941709285985395 9733721789912563928978093)
      ·
        refine ⟨3650145671217211473366785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9733721789912563928978093 3650145671217211473366785)
        ·
          refine ⟨2737609253412908605025089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650145671217211473366785 2737609253412908605025089)
          ·
            refine ⟨2053206940059681453768817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737609253412908605025089 2053206940059681453768817)
            ·
              refine ⟨1539905205044761090326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053206940059681453768817 1539905205044761090326613)
              ·
                refine ⟨18045764121618294027265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1539905205044761090326613 18045764121618294027265)
                ·
                  rfl

theorem cell22_474444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_474444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474444 prefixEnd_474444 := by exact prefixLift 474444
  have htrace : WordTrace (prefixWord ++ tailWord_474444) baseStart_474444 baseEnd_474444 := by
    simpa [prefixWord, tailWord_474444, baseEnd_474444] using wordTrace_append hprefix tailTrace_474444
  have hstable : (prefixWord ++ tailWord_474444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474444).length < 2 ^ (prefixWord ++ tailWord_474444).sum := by decide
  have hdescent : baseEnd_474444 < baseStart_474444 := by decide
  rcases family_descends (prefixWord ++ tailWord_474444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474446 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_474446 : Nat := 118140960795 + 474446 * 2 ^ 59
def prefixEnd_474446 : Nat := 4983230072969 + 3 ^ 40 * 474446 * 2
def baseEnd_474446 : Nat := 162412561735437307695379

theorem tailTrace_474446 : CollatzResearch.WordTrace tailWord_474446 prefixEnd_474446 162412561735437307695379 := by
  unfold tailWord_474446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163058404896330721358399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11536311492780430513911461 2163058404896330721358399)
  ·
    refine ⟨3244587607344496082037599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163058404896330721358399 3244587607344496082037599)
    ·
      refine ⟨4866881411016744123056399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244587607344496082037599 4866881411016744123056399)
      ·
        refine ⟨7300322116525116184584599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866881411016744123056399 7300322116525116184584599)
        ·
          refine ⟨10950483174787674276876899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300322116525116184584599 10950483174787674276876899)
          ·
            refine ⟨16425724762181511415315349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950483174787674276876899 16425724762181511415315349)
            ·
              refine ⟨769955848227258347592907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16425724762181511415315349 769955848227258347592907)
              ·
                refine ⟨1154933772340887521389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769955848227258347592907 1154933772340887521389361)
                ·
                  refine ⟨866200329255665641042021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154933772340887521389361 866200329255665641042021)
                  ·
                    refine ⟨162412561735437307695379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866200329255665641042021 162412561735437307695379)
                    ·
                      rfl

theorem cell22_474446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_474446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474446 prefixEnd_474446 := by exact prefixLift 474446
  have htrace : WordTrace (prefixWord ++ tailWord_474446) baseStart_474446 baseEnd_474446 := by
    simpa [prefixWord, tailWord_474446, baseEnd_474446] using wordTrace_append hprefix tailTrace_474446
  have hstable : (prefixWord ++ tailWord_474446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474446).length < 2 ^ (prefixWord ++ tailWord_474446).sum := by decide
  have hdescent : baseEnd_474446 < baseStart_474446 := by decide
  rcases family_descends (prefixWord ++ tailWord_474446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474585 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 4]
def baseStart_474585 : Nat := 118140960795 + 474585 * 2 ^ 59
def prefixEnd_474585 : Nat := 4983230072969 + 3 ^ 40 * 474585 * 2
def baseEnd_474585 : Nat := 54153381425362426156651

theorem tailTrace_474585 : CollatzResearch.WordTrace tailWord_474585 prefixEnd_474585 54153381425362426156651 := by
  unfold tailWord_474585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309536985667072510177209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11539691323778048340118139 17309536985667072510177209)
  ·
    refine ⟨12982152739250304382632907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17309536985667072510177209 12982152739250304382632907)
    ·
      refine ⟨19473229108875456573949361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982152739250304382632907 19473229108875456573949361)
      ·
        refine ⟨14604921831656592430462021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19473229108875456573949361 14604921831656592430462021)
        ·
          refine ⟨2738422843435611080711629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14604921831656592430462021 2738422843435611080711629)
          ·
            refine ⟨1026908566288354155266861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738422843435611080711629 1026908566288354155266861)
            ·
              refine ⟨385090712358132808225073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026908566288354155266861 385090712358132808225073)
              ·
                refine ⟨288818034268599606168805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385090712358132808225073 288818034268599606168805)
                ·
                  refine ⟨54153381425362426156651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288818034268599606168805 54153381425362426156651)
                  ·
                    rfl

theorem cell22_474585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_474585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474585 prefixEnd_474585 := by exact prefixLift 474585
  have htrace : WordTrace (prefixWord ++ tailWord_474585) baseStart_474585 baseEnd_474585 := by
    simpa [prefixWord, tailWord_474585, baseEnd_474585] using wordTrace_append hprefix tailTrace_474585
  have hstable : (prefixWord ++ tailWord_474585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474585).length < 2 ^ (prefixWord ++ tailWord_474585).sum := by decide
  have hdescent : baseEnd_474585 < baseStart_474585 := by decide
  rcases family_descends (prefixWord ++ tailWord_474585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474613 : List Nat := [1, 3, 5, 1, 1, 1, 2, 8]
def baseStart_474613 : Nat := 118140960795 + 474613 * 2 ^ 59
def prefixEnd_474613 : Nat := 4983230072969 + 3 ^ 40 * 474613 * 2
def baseEnd_474613 : Nat := 18052192138700504307763

theorem tailTrace_474613 : CollatzResearch.WordTrace tailWord_474613 prefixEnd_474613 18052192138700504307763 := by
  unfold tailWord_474613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17310558229565633292196493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11540372153043755528130995 17310558229565633292196493)
  ·
    refine ⟨6491459336087112484573685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17310558229565633292196493 6491459336087112484573685)
    ·
      refine ⟨608574312758166795428783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6491459336087112484573685 608574312758166795428783)
      ·
        refine ⟨912861469137250193143175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608574312758166795428783 912861469137250193143175)
        ·
          refine ⟨1369292203705875289714763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912861469137250193143175 1369292203705875289714763)
          ·
            refine ⟨2053938305558812934572145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369292203705875289714763 2053938305558812934572145)
            ·
              refine ⟨1540453729169109700929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053938305558812934572145 1540453729169109700929109)
              ·
                refine ⟨18052192138700504307763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1540453729169109700929109 18052192138700504307763)
                ·
                  rfl

theorem cell22_474613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 8].length) (baseStart_474613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474613 prefixEnd_474613 := by exact prefixLift 474613
  have htrace : WordTrace (prefixWord ++ tailWord_474613) baseStart_474613 baseEnd_474613 := by
    simpa [prefixWord, tailWord_474613, baseEnd_474613] using wordTrace_append hprefix tailTrace_474613
  have hstable : (prefixWord ++ tailWord_474613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474613).length < 2 ^ (prefixWord ++ tailWord_474613).sum := by decide
  have hdescent : baseEnd_474613 < baseStart_474613 := by decide
  rcases family_descends (prefixWord ++ tailWord_474613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474630 : List Nat := [6, 2, 1, 1, 12]
def baseStart_474630 : Nat := 118140960795 + 474630 * 2 ^ 59
def prefixEnd_474630 : Nat := 4983230072969 + 3 ^ 40 * 474630 * 2
def baseEnd_474630 : Nat := 668623657184041815205

theorem tailTrace_474630 : CollatzResearch.WordTrace tailWord_474630 prefixEnd_474630 668623657184041815205 := by
  unfold tailWord_474630
  simp only [CollatzResearch.WordTrace]
  refine ⟨540974320953251412361417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11540785513669363463710229 540974320953251412361417)
  ·
    refine ⟨405730740714938559271063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 540974320953251412361417 405730740714938559271063)
    ·
      refine ⟨608596111072407838906595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405730740714938559271063 608596111072407838906595)
      ·
        refine ⟨912894166608611758359893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608596111072407838906595 912894166608611758359893)
        ·
          refine ⟨668623657184041815205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 912894166608611758359893 668623657184041815205)
          ·
            rfl

theorem cell22_474630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 12].length) (baseStart_474630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474630 prefixEnd_474630 := by exact prefixLift 474630
  have htrace : WordTrace (prefixWord ++ tailWord_474630) baseStart_474630 baseEnd_474630 := by
    simpa [prefixWord, tailWord_474630, baseEnd_474630] using wordTrace_append hprefix tailTrace_474630
  have hstable : (prefixWord ++ tailWord_474630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474630).length < 2 ^ (prefixWord ++ tailWord_474630).sum := by decide
  have hdescent : baseEnd_474630 < baseStart_474630 := by decide
  rcases family_descends (prefixWord ++ tailWord_474630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474658 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_474658 : Nat := 118140960795 + 474658 * 2 ^ 59
def prefixEnd_474658 : Nat := 4983230072969 + 3 ^ 40 * 474658 * 2
def baseEnd_474658 : Nat := 54161711222646473798243

theorem tailTrace_474658 : CollatzResearch.WordTrace tailWord_474658 prefixEnd_474658 54161711222646473798243 := by
  unfold tailWord_474658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328049878600651494396157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11541466342935070651723085 4328049878600651494396157)
  ·
    refine ⟨1623018704475244310398559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4328049878600651494396157 1623018704475244310398559)
    ·
      refine ⟨2434528056712866465597839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623018704475244310398559 2434528056712866465597839)
      ·
        refine ⟨3651792085069299698396759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434528056712866465597839 3651792085069299698396759)
        ·
          refine ⟨5477688127603949547595139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651792085069299698396759 5477688127603949547595139)
          ·
            refine ⟨8216532191405924321392709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477688127603949547595139 8216532191405924321392709)
            ·
              refine ⟨1540599785888610810261133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8216532191405924321392709 1540599785888610810261133)
              ·
                refine ⟨577724919708229053847925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540599785888610810261133 577724919708229053847925)
                ·
                  refine ⟨54161711222646473798243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577724919708229053847925 54161711222646473798243)
                  ·
                    rfl

theorem cell22_474658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_474658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474658 prefixEnd_474658 := by exact prefixLift 474658
  have htrace : WordTrace (prefixWord ++ tailWord_474658) baseStart_474658 baseEnd_474658 := by
    simpa [prefixWord, tailWord_474658, baseEnd_474658] using wordTrace_append hprefix tailTrace_474658
  have hstable : (prefixWord ++ tailWord_474658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474658).length < 2 ^ (prefixWord ++ tailWord_474658).sum := by decide
  have hdescent : baseEnd_474658 < baseStart_474658 := by decide
  rcases family_descends (prefixWord ++ tailWord_474658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474810 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_474810 : Nat := 118140960795 + 474810 * 2 ^ 59
def prefixEnd_474810 : Nat := 4983230072969 + 3 ^ 40 * 474810 * 2
def baseEnd_474810 : Nat := 54179055458087230531421

theorem tailTrace_474810 : CollatzResearch.WordTrace tailWord_474810 prefixEnd_474810 54179055458087230531421 := by
  unfold tailWord_474810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329435852462983984279471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11545162273234623958078589 4329435852462983984279471)
  ·
    refine ⟨6494153778694475976419207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329435852462983984279471 6494153778694475976419207)
    ·
      refine ⟨9741230668041713964628811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494153778694475976419207 9741230668041713964628811)
      ·
        refine ⟨14611846002062570946943217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741230668041713964628811 14611846002062570946943217)
        ·
          refine ⟨10958884501546928210207413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14611846002062570946943217 10958884501546928210207413)
          ·
            refine ⟨1027395422020024519706945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10958884501546928210207413 1027395422020024519706945)
            ·
              refine ⟨770546566515018389780209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027395422020024519706945 770546566515018389780209)
              ·
                refine ⟨577909924886263792335157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770546566515018389780209 577909924886263792335157)
                ·
                  refine ⟨54179055458087230531421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577909924886263792335157 54179055458087230531421)
                  ·
                    rfl

theorem cell22_474810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_474810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474810 prefixEnd_474810 := by exact prefixLift 474810
  have htrace : WordTrace (prefixWord ++ tailWord_474810) baseStart_474810 baseEnd_474810 := by
    simpa [prefixWord, tailWord_474810, baseEnd_474810] using wordTrace_append hprefix tailTrace_474810
  have hstable : (prefixWord ++ tailWord_474810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474810).length < 2 ^ (prefixWord ++ tailWord_474810).sum := by decide
  have hdescent : baseEnd_474810 < baseStart_474810 := by decide
  rcases family_descends (prefixWord ++ tailWord_474810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474814 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_474814 : Nat := 118140960795 + 474814 * 2 ^ 59
def prefixEnd_474814 : Nat := 4983230072969 + 3 ^ 40 * 474814 * 2
def baseEnd_474814 : Nat := 162538535656007014494251

theorem tailTrace_474814 : CollatzResearch.WordTrace tailWord_474814 prefixEnd_474814 162538535656007014494251 := by
  unfold tailWord_474814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164736162729680577532937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11545259534558296413508997 2164736162729680577532937)
  ·
    refine ⟨1623552122047260433149703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2164736162729680577532937 1623552122047260433149703)
    ·
      refine ⟨2435328183070890649724555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623552122047260433149703 2435328183070890649724555)
      ·
        refine ⟨3652992274606335974586833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435328183070890649724555 3652992274606335974586833)
        ·
          refine ⟨2739744205954751980940125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652992274606335974586833 2739744205954751980940125)
          ·
            refine ⟨1027404077233031992852547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2739744205954751980940125 1027404077233031992852547)
            ·
              refine ⟨1541106115849547989278821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027404077233031992852547 1541106115849547989278821)
              ·
                refine ⟨288957396721790247989779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1541106115849547989278821 288957396721790247989779)
                ·
                  refine ⟨433436095082685371984669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288957396721790247989779 433436095082685371984669)
                  ·
                    refine ⟨162538535656007014494251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433436095082685371984669 162538535656007014494251)
                    ·
                      rfl

theorem cell22_474814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_474814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474814 prefixEnd_474814 := by exact prefixLift 474814
  have htrace : WordTrace (prefixWord ++ tailWord_474814) baseStart_474814 baseEnd_474814 := by
    simpa [prefixWord, tailWord_474814, baseEnd_474814] using wordTrace_append hprefix tailTrace_474814
  have hstable : (prefixWord ++ tailWord_474814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474814).length < 2 ^ (prefixWord ++ tailWord_474814).sum := by decide
  have hdescent : baseEnd_474814 < baseStart_474814 := by decide
  rcases family_descends (prefixWord ++ tailWord_474814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474823 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_474823 : Nat := 118140960795 + 474823 * 2 ^ 59
def prefixEnd_474823 : Nat := 4983230072969 + 3 ^ 40 * 474823 * 2
def baseEnd_474823 : Nat := 162541616539933991019223

theorem tailTrace_474823 : CollatzResearch.WordTrace tailWord_474823 prefixEnd_474823 162541616539933991019223 := by
  unfold tailWord_474823
  simp only [CollatzResearch.WordTrace]
  refine ⟨17318217558804839157341123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11545478372536559438227415 17318217558804839157341123)
  ·
    refine ⟨25977326338207258736011685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17318217558804839157341123 25977326338207258736011685)
    ·
      refine ⟨4870748688413861013002191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25977326338207258736011685 4870748688413861013002191)
      ·
        refine ⟨7306123032620791519503287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870748688413861013002191 7306123032620791519503287)
        ·
          refine ⟨10959184548931187279254931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306123032620791519503287 10959184548931187279254931)
          ·
            refine ⟨16438776823396780918882397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10959184548931187279254931 16438776823396780918882397)
            ·
              refine ⟨6164541308773792844580899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16438776823396780918882397 6164541308773792844580899)
              ·
                refine ⟨9246811963160689266871349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164541308773792844580899 9246811963160689266871349)
                ·
                  refine ⟨866888621546314618769189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9246811963160689266871349 866888621546314618769189)
                  ·
                    refine ⟨162541616539933991019223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866888621546314618769189 162541616539933991019223)
                    ·
                      rfl

theorem cell22_474823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_474823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474823 prefixEnd_474823 := by exact prefixLift 474823
  have htrace : WordTrace (prefixWord ++ tailWord_474823) baseStart_474823 baseEnd_474823 := by
    simpa [prefixWord, tailWord_474823, baseEnd_474823] using wordTrace_append hprefix tailTrace_474823
  have hstable : (prefixWord ++ tailWord_474823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474823).length < 2 ^ (prefixWord ++ tailWord_474823).sum := by decide
  have hdescent : baseEnd_474823 < baseStart_474823 := by decide
  rcases family_descends (prefixWord ++ tailWord_474823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474840 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_474840 : Nat := 118140960795 + 474840 * 2 ^ 59
def prefixEnd_474840 : Nat := 4983230072969 + 3 ^ 40 * 474840 * 2
def baseEnd_474840 : Nat := 162547435987351613344171

theorem tailTrace_474840 : CollatzResearch.WordTrace tailWord_474840 prefixEnd_474840 162547435987351613344171 := by
  unfold tailWord_474840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659418799871625530354987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11545891733162167373806649 8659418799871625530354987)
  ·
    refine ⟨12989128199807438295532481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8659418799871625530354987 12989128199807438295532481)
    ·
      refine ⟨9741846149855578721649361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12989128199807438295532481 9741846149855578721649361)
      ·
        refine ⟨7306384612391684041237021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741846149855578721649361 7306384612391684041237021)
        ·
          refine ⟨2739894229646881515463883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7306384612391684041237021 2739894229646881515463883)
          ·
            refine ⟨4109841344470322273195825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739894229646881515463883 4109841344470322273195825)
            ·
              refine ⟨3082381008352741704896869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109841344470322273195825 3082381008352741704896869)
              ·
                refine ⟨577946439066139069668163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3082381008352741704896869 577946439066139069668163)
                ·
                  refine ⟨866919658599208604502245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577946439066139069668163 866919658599208604502245)
                  ·
                    refine ⟨162547435987351613344171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866919658599208604502245 162547435987351613344171)
                    ·
                      rfl

theorem cell22_474840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_474840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474840 prefixEnd_474840 := by exact prefixLift 474840
  have htrace : WordTrace (prefixWord ++ tailWord_474840) baseStart_474840 baseEnd_474840 := by
    simpa [prefixWord, tailWord_474840, baseEnd_474840] using wordTrace_append hprefix tailTrace_474840
  have hstable : (prefixWord ++ tailWord_474840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474840).length < 2 ^ (prefixWord ++ tailWord_474840).sum := by decide
  have hdescent : baseEnd_474840 < baseStart_474840 := by decide
  rcases family_descends (prefixWord ++ tailWord_474840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474915 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 5, 3]
def baseStart_474915 : Nat := 118140960795 + 474915 * 2 ^ 59
def prefixEnd_474915 : Nat := 4983230072969 + 3 ^ 40 * 474915 * 2
def baseEnd_474915 : Nat := 162573110020076417718941

theorem tailTrace_474915 : CollatzResearch.WordTrace tailWord_474915 prefixEnd_474915 162573110020076417718941 := by
  unfold tailWord_474915
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321573074471538869690199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11547715382981025913126799 17321573074471538869690199)
  ·
    refine ⟨25982359611707308304535299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17321573074471538869690199 25982359611707308304535299)
    ·
      refine ⟨38973539417560962456802949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25982359611707308304535299 38973539417560962456802949)
      ·
        refine ⟨7307538640792680460650553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38973539417560962456802949 7307538640792680460650553)
        ·
          refine ⟨5480653980594510345487915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7307538640792680460650553 5480653980594510345487915)
          ·
            refine ⟨8220980970891765518231873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480653980594510345487915 8220980970891765518231873)
            ·
              refine ⟨6165735728168824138673905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220980970891765518231873 6165735728168824138673905)
              ·
                refine ⟨4624301796126618104005429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165735728168824138673905 4624301796126618104005429)
                ·
                  refine ⟨433528293386870447250509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624301796126618104005429 433528293386870447250509)
                  ·
                    refine ⟨162573110020076417718941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433528293386870447250509 162573110020076417718941)
                    ·
                      rfl

theorem cell22_474915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].length) (baseStart_474915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_474915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_474915 prefixEnd_474915 := by exact prefixLift 474915
  have htrace : WordTrace (prefixWord ++ tailWord_474915) baseStart_474915 baseEnd_474915 := by
    simpa [prefixWord, tailWord_474915, baseEnd_474915] using wordTrace_append hprefix tailTrace_474915
  have hstable : (prefixWord ++ tailWord_474915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474915).length < 2 ^ (prefixWord ++ tailWord_474915).sum := by decide
  have hdescent : baseEnd_474915 < baseStart_474915 := by decide
  rcases family_descends (prefixWord ++ tailWord_474915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475026 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_475026 : Nat := 118140960795 + 475026 * 2 ^ 59
def prefixEnd_475026 : Nat := 4983230072969 + 3 ^ 40 * 475026 * 2
def baseEnd_475026 : Nat := 162611107588509128193601

theorem tailTrace_475026 : CollatzResearch.WordTrace tailWord_475026 prefixEnd_475026 162611107588509128193601 := by
  unfold tailWord_475026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331405394267351206745233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11550414384712936551320621 4331405394267351206745233)
  ·
    refine ⟨3248554045700513405058925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4331405394267351206745233 3248554045700513405058925)
    ·
      refine ⟨1218207767137692526897097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3248554045700513405058925 1218207767137692526897097)
      ·
        refine ⟨913655825353269395172823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1218207767137692526897097 913655825353269395172823)
        ·
          refine ⟨1370483738029904092759235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913655825353269395172823 1370483738029904092759235)
          ·
            refine ⟨2055725607044856139138853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370483738029904092759235 2055725607044856139138853)
            ·
              refine ⟨385448551320910526088535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2055725607044856139138853 385448551320910526088535)
              ·
                refine ⟨578172826981365789132803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385448551320910526088535 578172826981365789132803)
                ·
                  refine ⟨867259240472048683699205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578172826981365789132803 867259240472048683699205)
                  ·
                    refine ⟨162611107588509128193601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 867259240472048683699205 162611107588509128193601)
                    ·
                      rfl

theorem cell22_475026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_475026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475026 prefixEnd_475026 := by exact prefixLift 475026
  have htrace : WordTrace (prefixWord ++ tailWord_475026) baseStart_475026 baseEnd_475026 := by
    simpa [prefixWord, tailWord_475026, baseEnd_475026] using wordTrace_append hprefix tailTrace_475026
  have hstable : (prefixWord ++ tailWord_475026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475026).length < 2 ^ (prefixWord ++ tailWord_475026).sum := by decide
  have hdescent : baseEnd_475026 < baseStart_475026 := by decide
  rcases family_descends (prefixWord ++ tailWord_475026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475030 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_475030 : Nat := 118140960795 + 475030 * 2 ^ 59
def prefixEnd_475030 : Nat := 4983230072969 + 3 ^ 40 * 475030 * 2
def baseEnd_475030 : Nat := 54204158956751483697863

theorem tailTrace_475030 : CollatzResearch.WordTrace tailWord_475030 prefixEnd_475030 54204158956751483697863 := by
  unfold tailWord_475030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082860466815932094382909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11550511646036609006751029 1082860466815932094382909)
  ·
    refine ⟨406072675055974535393591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1082860466815932094382909 406072675055974535393591)
    ·
      refine ⟨609109012583961803090387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406072675055974535393591 609109012583961803090387)
      ·
        refine ⟨913663518875942704635581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609109012583961803090387 913663518875942704635581)
        ·
          refine ⟨342623819578478514238343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 913663518875942704635581 342623819578478514238343)
          ·
            refine ⟨513935729367717771357515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342623819578478514238343 513935729367717771357515)
            ·
              refine ⟨770903594051576657036273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513935729367717771357515 770903594051576657036273)
              ·
                refine ⟨578177695538682492777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770903594051576657036273 578177695538682492777205)
                ·
                  refine ⟨54204158956751483697863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578177695538682492777205 54204158956751483697863)
                  ·
                    rfl

theorem cell22_475030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_475030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475030 prefixEnd_475030 := by exact prefixLift 475030
  have htrace : WordTrace (prefixWord ++ tailWord_475030) baseStart_475030 baseEnd_475030 := by
    simpa [prefixWord, tailWord_475030, baseEnd_475030] using wordTrace_append hprefix tailTrace_475030
  have hstable : (prefixWord ++ tailWord_475030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475030).length < 2 ^ (prefixWord ++ tailWord_475030).sum := by decide
  have hdescent : baseEnd_475030 < baseStart_475030 := by decide
  rcases family_descends (prefixWord ++ tailWord_475030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475039 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 4, 3]
def baseStart_475039 : Nat := 118140960795 + 475039 * 2 ^ 59
def prefixEnd_475039 : Nat := 4983230072969 + 3 ^ 40 * 475039 * 2
def baseEnd_475039 : Nat := 162615557754181427618561

theorem tailTrace_475039 : CollatzResearch.WordTrace tailWord_475039 prefixEnd_475039 162615557754181427618561 := by
  unfold tailWord_475039
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326095726022308047204171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11550730484014872031469447 17326095726022308047204171)
  ·
    refine ⟨25989143589033462070806257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17326095726022308047204171 25989143589033462070806257)
    ·
      refine ⟨19491857691775096553104693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25989143589033462070806257 19491857691775096553104693)
      ·
        refine ⟨1827361658603915301853565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19491857691775096553104693 1827361658603915301853565)
        ·
          refine ⟨685260621976468238195087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1827361658603915301853565 685260621976468238195087)
          ·
            refine ⟨1027890932964702357292631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685260621976468238195087 1027890932964702357292631)
            ·
              refine ⟨1541836399447053535938947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027890932964702357292631 1541836399447053535938947)
              ·
                refine ⟨2312754599170580303908421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541836399447053535938947 2312754599170580303908421)
                ·
                  refine ⟨433641487344483806982829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312754599170580303908421 433641487344483806982829)
                  ·
                    refine ⟨162615557754181427618561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433641487344483806982829 162615557754181427618561)
                    ·
                      rfl

theorem cell22_475039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_475039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475039 prefixEnd_475039 := by exact prefixLift 475039
  have htrace : WordTrace (prefixWord ++ tailWord_475039) baseStart_475039 baseEnd_475039 := by
    simpa [prefixWord, tailWord_475039, baseEnd_475039] using wordTrace_append hprefix tailTrace_475039
  have hstable : (prefixWord ++ tailWord_475039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475039).length < 2 ^ (prefixWord ++ tailWord_475039).sum := by decide
  have hdescent : baseEnd_475039 < baseStart_475039 := by decide
  rcases family_descends (prefixWord ++ tailWord_475039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475069 : List Nat := [1, 4, 1, 2, 3, 3, 2, 6]
def baseStart_475069 : Nat := 118140960795 + 475069 * 2 ^ 59
def prefixEnd_475069 : Nat := 4983230072969 + 3 ^ 40 * 475069 * 2
def baseEnd_475069 : Nat := 18069536374141261040941

theorem tailTrace_475069 : CollatzResearch.WordTrace tailWord_475069 prefixEnd_475069 18069536374141261040941 := by
  unfold tailWord_475069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17327189915913623170796261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11551459943942415447197507 17327189915913623170796261)
  ·
    refine ⟨3248848109233804344524299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17327189915913623170796261 3248848109233804344524299)
    ·
      refine ⟨4873272163850706516786449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248848109233804344524299 4873272163850706516786449)
      ·
        refine ⟨3654954122888029887589837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873272163850706516786449 3654954122888029887589837)
        ·
          refine ⟨1370607796083011207846189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3654954122888029887589837 1370607796083011207846189)
          ·
            refine ⟨513977923531129202942321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1370607796083011207846189 513977923531129202942321)
            ·
              refine ⟨385483442648346902206741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513977923531129202942321 385483442648346902206741)
              ·
                refine ⟨18069536374141261040941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385483442648346902206741 18069536374141261040941)
                ·
                  rfl

theorem cell22_475069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 6].length) (baseStart_475069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475069 prefixEnd_475069 := by exact prefixLift 475069
  have htrace : WordTrace (prefixWord ++ tailWord_475069) baseStart_475069 baseEnd_475069 := by
    simpa [prefixWord, tailWord_475069, baseEnd_475069] using wordTrace_append hprefix tailTrace_475069
  have hstable : (prefixWord ++ tailWord_475069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475069).length < 2 ^ (prefixWord ++ tailWord_475069).sum := by decide
  have hdescent : baseEnd_475069 < baseStart_475069 := by decide
  rcases family_descends (prefixWord ++ tailWord_475069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475176 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_475176 : Nat := 118140960795 + 475176 * 2 ^ 59
def prefixEnd_475176 : Nat := 4983230072969 + 3 ^ 40 * 475176 * 2
def baseEnd_475176 : Nat := 54220818551319578981047

theorem tailTrace_475176 : CollatzResearch.WordTrace tailWord_475176 prefixEnd_475176 54220818551319578981047 := by
  unfold tailWord_475176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665546263262990222470691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11554061684350653629960921 8665546263262990222470691)
  ·
    refine ⟨12998319394894485333706037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8665546263262990222470691 12998319394894485333706037)
    ·
      refine ⟨1218592443271358000034941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12998319394894485333706037 1218592443271358000034941)
      ·
        refine ⟨456972166226759250013103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1218592443271358000034941 456972166226759250013103)
        ·
          refine ⟨685458249340138875019655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456972166226759250013103 685458249340138875019655)
          ·
            refine ⟨1028187374010208312529483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685458249340138875019655 1028187374010208312529483)
            ·
              refine ⟨1542281061015312468794225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028187374010208312529483 1542281061015312468794225)
              ·
                refine ⟨1156710795761484351595669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542281061015312468794225 1156710795761484351595669)
                ·
                  refine ⟨54220818551319578981047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1156710795761484351595669 54220818551319578981047)
                  ·
                    rfl

theorem cell22_475176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_475176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475176 prefixEnd_475176 := by exact prefixLift 475176
  have htrace : WordTrace (prefixWord ++ tailWord_475176) baseStart_475176 baseEnd_475176 := by
    simpa [prefixWord, tailWord_475176, baseEnd_475176] using wordTrace_append hprefix tailTrace_475176
  have hstable : (prefixWord ++ tailWord_475176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475176).length < 2 ^ (prefixWord ++ tailWord_475176).sum := by decide
  have hdescent : baseEnd_475176 < baseStart_475176 := by decide
  rcases family_descends (prefixWord ++ tailWord_475176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475189 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_475189 : Nat := 118140960795 + 475189 * 2 ^ 59
def prefixEnd_475189 : Nat := 4983230072969 + 3 ^ 40 * 475189 * 2
def baseEnd_475189 : Nat := 162666905819631036368101

theorem tailTrace_475189 : CollatzResearch.WordTrace tailWord_475189 prefixEnd_475189 162666905819631036368101 := by
  unfold tailWord_475189
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331566675478883665164621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11554377783652589110109747 17331566675478883665164621)
  ·
    refine ⟨6499337503304581374436733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17331566675478883665164621 6499337503304581374436733)
    ·
      refine ⟨2437251563739218015413775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6499337503304581374436733 2437251563739218015413775)
      ·
        refine ⟨3655877345608827023120663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437251563739218015413775 3655877345608827023120663)
        ·
          refine ⟨5483816018413240534680995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655877345608827023120663 5483816018413240534680995)
          ·
            refine ⟨8225724027619860802021493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483816018413240534680995 8225724027619860802021493)
            ·
              refine ⟨771161627589361950189515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8225724027619860802021493 771161627589361950189515)
              ·
                refine ⟨1156742441384042925284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771161627589361950189515 1156742441384042925284273)
                ·
                  refine ⟨867556831038032193963205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156742441384042925284273 867556831038032193963205)
                  ·
                    refine ⟨162666905819631036368101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 867556831038032193963205 162666905819631036368101)
                    ·
                      rfl

theorem cell22_475189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_475189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475189 prefixEnd_475189 := by exact prefixLift 475189
  have htrace : WordTrace (prefixWord ++ tailWord_475189) baseStart_475189 baseEnd_475189 := by
    simpa [prefixWord, tailWord_475189, baseEnd_475189] using wordTrace_append hprefix tailTrace_475189
  have hstable : (prefixWord ++ tailWord_475189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475189).length < 2 ^ (prefixWord ++ tailWord_475189).sum := by decide
  have hdescent : baseEnd_475189 < baseStart_475189 := by decide
  rcases family_descends (prefixWord ++ tailWord_475189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475206 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_475206 : Nat := 118140960795 + 475206 * 2 ^ 59
def prefixEnd_475206 : Nat := 4983230072969 + 3 ^ 40 * 475206 * 2
def baseEnd_475206 : Nat := 162672725267048658693049

theorem tailTrace_475206 : CollatzResearch.WordTrace tailWord_475206 prefixEnd_475206 162672725267048658693049 := by
  unfold tailWord_475206
  simp only [CollatzResearch.WordTrace]
  refine ⟨541630834888040486516671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11554791144278197045688981 541630834888040486516671)
  ·
    refine ⟨812446252332060729775007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541630834888040486516671 812446252332060729775007)
    ·
      refine ⟨1218669378498091094662511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812446252332060729775007 1218669378498091094662511)
      ·
        refine ⟨1828004067747136641993767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218669378498091094662511 1828004067747136641993767)
        ·
          refine ⟨2742006101620704962990651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828004067747136641993767 2742006101620704962990651)
          ·
            refine ⟨4113009152431057444485977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742006101620704962990651 4113009152431057444485977)
            ·
              refine ⟨3084756864323293083364483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113009152431057444485977 3084756864323293083364483)
              ·
                refine ⟨4627135296484939625046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084756864323293083364483 4627135296484939625046725)
                ·
                  refine ⟨867587868090926179696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4627135296484939625046725 867587868090926179696261)
                  ·
                    refine ⟨162672725267048658693049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 867587868090926179696261 162672725267048658693049)
                    ·
                      rfl

theorem cell22_475206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_475206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475206 prefixEnd_475206 := by exact prefixLift 475206
  have htrace : WordTrace (prefixWord ++ tailWord_475206) baseStart_475206 baseEnd_475206 := by
    simpa [prefixWord, tailWord_475206, baseEnd_475206] using wordTrace_append hprefix tailTrace_475206
  have hstable : (prefixWord ++ tailWord_475206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475206).length < 2 ^ (prefixWord ++ tailWord_475206).sum := by decide
  have hdescent : baseEnd_475206 < baseStart_475206 := by decide
  rcases family_descends (prefixWord ++ tailWord_475206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475296 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_475296 : Nat := 118140960795 + 475296 * 2 ^ 59
def prefixEnd_475296 : Nat := 4983230072969 + 3 ^ 40 * 475296 * 2
def baseEnd_475296 : Nat := 162703534106318423942773

theorem tailTrace_475296 : CollatzResearch.WordTrace tailWord_475296 prefixEnd_475296 162703534106318423942773 := by
  unfold tailWord_475296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667734643045620469654871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11556979524060827292873161 8667734643045620469654871)
  ·
    refine ⟨13001601964568430704482307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8667734643045620469654871 13001601964568430704482307)
    ·
      refine ⟨19502402946852646056723461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001601964568430704482307 19502402946852646056723461)
      ·
        refine ⟨3656700552534871135635649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19502402946852646056723461 3656700552534871135635649)
        ·
          refine ⟨2742525414401153351726737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656700552534871135635649 2742525414401153351726737)
          ·
            refine ⟨2056894060800865013795053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742525414401153351726737 2056894060800865013795053)
            ·
              refine ⟨771335272800324380173145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2056894060800865013795053 771335272800324380173145)
              ·
                refine ⟨578501454600243285129859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771335272800324380173145 578501454600243285129859)
                ·
                  refine ⟨867752181900364927694789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578501454600243285129859 867752181900364927694789)
                  ·
                    refine ⟨162703534106318423942773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 867752181900364927694789 162703534106318423942773)
                    ·
                      rfl

theorem cell22_475296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_475296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475296 prefixEnd_475296 := by exact prefixLift 475296
  have htrace : WordTrace (prefixWord ++ tailWord_475296) baseStart_475296 baseEnd_475296 := by
    simpa [prefixWord, tailWord_475296, baseEnd_475296] using wordTrace_append hprefix tailTrace_475296
  have hstable : (prefixWord ++ tailWord_475296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475296).length < 2 ^ (prefixWord ++ tailWord_475296).sum := by decide
  have hdescent : baseEnd_475296 < baseStart_475296 := by decide
  rcases family_descends (prefixWord ++ tailWord_475296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475307 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_475307 : Nat := 118140960795 + 475307 * 2 ^ 59
def prefixEnd_475307 : Nat := 4983230072969 + 3 ^ 40 * 475307 * 2
def baseEnd_475307 : Nat := 162707299631118061917739

theorem tailTrace_475307 : CollatzResearch.WordTrace tailWord_475307 prefixEnd_475307 162707299631118061917739 := by
  unfold tailWord_475307
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335870489051389817960175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11557246992700926545306783 17335870489051389817960175)
  ·
    refine ⟨26003805733577084726940263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17335870489051389817960175 26003805733577084726940263)
    ·
      refine ⟨39005708600365627090410395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26003805733577084726940263 39005708600365627090410395)
      ·
        refine ⟨58508562900548440635615593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39005708600365627090410395 58508562900548440635615593)
        ·
          refine ⟨43881422175411330476711695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58508562900548440635615593 43881422175411330476711695)
          ·
            refine ⟨65822133263116995715067543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43881422175411330476711695 65822133263116995715067543)
            ·
              refine ⟨98733199894675493572601315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65822133263116995715067543 98733199894675493572601315)
              ·
                refine ⟨148099799842013240358901973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98733199894675493572601315 148099799842013240358901973)
                ·
                  refine ⟨3471089058797185320911765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148099799842013240358901973 3471089058797185320911765)
                  ·
                    refine ⟨162707299631118061917739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3471089058797185320911765 162707299631118061917739)
                    ·
                      rfl

theorem cell22_475307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_475307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475307 prefixEnd_475307 := by exact prefixLift 475307
  have htrace : WordTrace (prefixWord ++ tailWord_475307) baseStart_475307 baseEnd_475307 := by
    simpa [prefixWord, tailWord_475307, baseEnd_475307] using wordTrace_append hprefix tailTrace_475307
  have hstable : (prefixWord ++ tailWord_475307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475307).length < 2 ^ (prefixWord ++ tailWord_475307).sum := by decide
  have hdescent : baseEnd_475307 < baseStart_475307 := by decide
  rcases family_descends (prefixWord ++ tailWord_475307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475328 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_475328 : Nat := 118140960795 + 475328 * 2 ^ 59
def prefixEnd_475328 : Nat := 4983230072969 + 3 ^ 40 * 475328 * 2
def baseEnd_475328 : Nat := 54238162786760335714225

theorem tailTrace_475328 : CollatzResearch.WordTrace tailWord_475328 prefixEnd_475328 54238162786760335714225 := by
  unfold tailWord_475328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668318210987655202237319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11557757614650206936316425 8668318210987655202237319)
  ·
    refine ⟨13002477316481482803355979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8668318210987655202237319 13002477316481482803355979)
    ·
      refine ⟨19503715974722224205033969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002477316481482803355979 19503715974722224205033969)
      ·
        refine ⟨14627786981041668153775477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503715974722224205033969 14627786981041668153775477)
        ·
          refine ⟨1371355029472656389416451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14627786981041668153775477 1371355029472656389416451)
          ·
            refine ⟨2057032544208984584124677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371355029472656389416451 2057032544208984584124677)
            ·
              refine ⟨385693602039184609523377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2057032544208984584124677 385693602039184609523377)
              ·
                refine ⟨289270201529388457142533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385693602039184609523377 289270201529388457142533)
                ·
                  refine ⟨54238162786760335714225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289270201529388457142533 54238162786760335714225)
                  ·
                    rfl

theorem cell22_475328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_475328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475328 prefixEnd_475328 := by exact prefixLift 475328
  have htrace : WordTrace (prefixWord ++ tailWord_475328) baseStart_475328 baseEnd_475328 := by
    simpa [prefixWord, tailWord_475328, baseEnd_475328] using wordTrace_append hprefix tailTrace_475328
  have hstable : (prefixWord ++ tailWord_475328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475328).length < 2 ^ (prefixWord ++ tailWord_475328).sum := by decide
  have hdescent : baseEnd_475328 < baseStart_475328 := by decide
  rcases family_descends (prefixWord ++ tailWord_475328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475388 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_475388 : Nat := 118140960795 + 475388 * 2 ^ 59
def prefixEnd_475388 : Nat := 4983230072969 + 3 ^ 40 * 475388 * 2
def baseEnd_475388 : Nat := 162735027586460850642491

theorem tailTrace_475388 : CollatzResearch.WordTrace tailWord_475388 prefixEnd_475388 162735027586460850642491 := by
  unfold tailWord_475388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669412400878970325829409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11559216534505293767772545 8669412400878970325829409)
  ·
    refine ⟨6502059300659227744372057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8669412400878970325829409 6502059300659227744372057)
    ·
      refine ⟨4876544475494420808279043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6502059300659227744372057 4876544475494420808279043)
      ·
        refine ⟨7314816713241631212418565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876544475494420808279043 7314816713241631212418565)
        ·
          refine ⟨1371528133732805852328481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7314816713241631212418565 1371528133732805852328481)
          ·
            refine ⟨1028646100299604389246361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371528133732805852328481 1028646100299604389246361)
            ·
              refine ⟨771484575224703291934771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028646100299604389246361 771484575224703291934771)
              ·
                refine ⟨1157226862837054937902157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771484575224703291934771 1157226862837054937902157)
                ·
                  refine ⟨433960073563895601713309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157226862837054937902157 433960073563895601713309)
                  ·
                    refine ⟨162735027586460850642491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433960073563895601713309 162735027586460850642491)
                    ·
                      rfl

theorem cell22_475388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_475388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475388 prefixEnd_475388 := by exact prefixLift 475388
  have htrace : WordTrace (prefixWord ++ tailWord_475388) baseStart_475388 baseEnd_475388 := by
    simpa [prefixWord, tailWord_475388, baseEnd_475388] using wordTrace_append hprefix tailTrace_475388
  have hstable : (prefixWord ++ tailWord_475388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475388).length < 2 ^ (prefixWord ++ tailWord_475388).sum := by decide
  have hdescent : baseEnd_475388 < baseStart_475388 := by decide
  rcases family_descends (prefixWord ++ tailWord_475388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475459 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_475459 : Nat := 118140960795 + 475459 * 2 ^ 59
def prefixEnd_475459 : Nat := 4983230072969 + 3 ^ 40 * 475459 * 2
def baseEnd_475459 : Nat := 162759332337440332117273

theorem tailTrace_475459 : CollatzResearch.WordTrace tailWord_475459 prefixEnd_475459 162759332337440332117273 := by
  unfold tailWord_475459
  simp only [CollatzResearch.WordTrace]
  refine ⟨17341414384500719777493431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11560942923000479851662287 17341414384500719777493431)
  ·
    refine ⟨26012121576751079666240147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17341414384500719777493431 26012121576751079666240147)
    ·
      refine ⟨39018182365126619499360221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012121576751079666240147 39018182365126619499360221)
      ·
        refine ⟨14631818386922482312260083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39018182365126619499360221 14631818386922482312260083)
        ·
          refine ⟨21947727580383723468390125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631818386922482312260083 21947727580383723468390125)
          ·
            refine ⟨8230397842643896300646297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21947727580383723468390125 8230397842643896300646297)
            ·
              refine ⟨6172798381982922225484723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8230397842643896300646297 6172798381982922225484723)
              ·
                refine ⟨9259197572974383338227085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172798381982922225484723 9259197572974383338227085)
                ·
                  refine ⟨3472199089865393751835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9259197572974383338227085 3472199089865393751835157)
                  ·
                    refine ⟨162759332337440332117273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3472199089865393751835157 162759332337440332117273)
                    ·
                      rfl

theorem cell22_475459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_475459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475459 prefixEnd_475459 := by exact prefixLift 475459
  have htrace : WordTrace (prefixWord ++ tailWord_475459) baseStart_475459 baseEnd_475459 := by
    simpa [prefixWord, tailWord_475459, baseEnd_475459] using wordTrace_append hprefix tailTrace_475459
  have hstable : (prefixWord ++ tailWord_475459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475459).length < 2 ^ (prefixWord ++ tailWord_475459).sum := by decide
  have hdescent : baseEnd_475459 < baseStart_475459 := by decide
  rcases family_descends (prefixWord ++ tailWord_475459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475495 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 2, 3]
def baseStart_475495 : Nat := 118140960795 + 475495 * 2 ^ 59
def prefixEnd_475495 : Nat := 4983230072969 + 3 ^ 40 * 475495 * 2
def baseEnd_475495 : Nat := 162771655873148238217163

theorem tailTrace_475495 : CollatzResearch.WordTrace tailWord_475495 prefixEnd_475495 162771655873148238217163 := by
  unfold tailWord_475495
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342727412370297925803939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11561818274913531950535959 17342727412370297925803939)
  ·
    refine ⟨26014091118555446888705909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17342727412370297925803939 26014091118555446888705909)
    ·
      refine ⟨2438821042364573145816179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26014091118555446888705909 2438821042364573145816179)
      ·
        refine ⟨3658231563546859718724269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438821042364573145816179 3658231563546859718724269)
        ·
          refine ⟨1371836836330072394521601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3658231563546859718724269 1371836836330072394521601)
          ·
            refine ⟨1028877627247554295891201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371836836330072394521601 1028877627247554295891201)
            ·
              refine ⟨771658220435665721918401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028877627247554295891201 771658220435665721918401)
              ·
                refine ⟨578743665326749291438801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771658220435665721918401 578743665326749291438801)
                ·
                  refine ⟨434057748995061968579101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578743665326749291438801 434057748995061968579101)
                  ·
                    refine ⟨162771655873148238217163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434057748995061968579101 162771655873148238217163)
                    ·
                      rfl

theorem cell22_475495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_475495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475495 prefixEnd_475495 := by exact prefixLift 475495
  have htrace : WordTrace (prefixWord ++ tailWord_475495) baseStart_475495 baseEnd_475495 := by
    simpa [prefixWord, tailWord_475495, baseEnd_475495] using wordTrace_append hprefix tailTrace_475495
  have hstable : (prefixWord ++ tailWord_475495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475495).length < 2 ^ (prefixWord ++ tailWord_475495).sum := by decide
  have hdescent : baseEnd_475495 < baseStart_475495 := by decide
  rcases family_descends (prefixWord ++ tailWord_475495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475542 : List Nat := [5, 3, 1, 2, 1, 1, 9]
def baseStart_475542 : Nat := 118140960795 + 475542 * 2 ^ 59
def prefixEnd_475542 : Nat := 4983230072969 + 3 ^ 40 * 475542 * 2
def baseEnd_475542 : Nat := 6029175738283547492297

theorem tailTrace_475542 : CollatzResearch.WordTrace tailWord_475542 prefixEnd_475542 6029175738283547492297 := by
  unfold tailWord_475542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084027602700001559547805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11562961095466683301843253 1084027602700001559547805)
  ·
    refine ⟨406510351012500584830427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1084027602700001559547805 406510351012500584830427)
    ·
      refine ⟨609765526518750877245641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406510351012500584830427 609765526518750877245641)
      ·
        refine ⟨457324144889063157934231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609765526518750877245641 457324144889063157934231)
        ·
          refine ⟨685986217333594736901347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457324144889063157934231 685986217333594736901347)
          ·
            refine ⟨1028979326000392105352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685986217333594736901347 1028979326000392105352021)
            ·
              refine ⟨6029175738283547492297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1028979326000392105352021 6029175738283547492297)
              ·
                rfl

theorem cell22_475542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 9].length) (baseStart_475542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475542 prefixEnd_475542 := by exact prefixLift 475542
  have htrace : WordTrace (prefixWord ++ tailWord_475542) baseStart_475542 baseEnd_475542 := by
    simpa [prefixWord, tailWord_475542, baseEnd_475542] using wordTrace_append hprefix tailTrace_475542
  have hstable : (prefixWord ++ tailWord_475542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475542).length < 2 ^ (prefixWord ++ tailWord_475542).sum := by decide
  have hdescent : baseEnd_475542 < baseStart_475542 := by decide
  rcases family_descends (prefixWord ++ tailWord_475542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475551 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_475551 : Nat := 118140960795 + 475551 * 2 ^ 59
def prefixEnd_475551 : Nat := 4983230072969 + 3 ^ 40 * 475551 * 2
def baseEnd_475551 : Nat := 162790825817582758816991

theorem tailTrace_475551 : CollatzResearch.WordTrace tailWord_475551 prefixEnd_475551 162790825817582758816991 := by
  unfold tailWord_475551
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344769900167419489842507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11563179933444946326561671 17344769900167419489842507)
  ·
    refine ⟨26017154850251129234763761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17344769900167419489842507 26017154850251129234763761)
    ·
      refine ⟨19512866137688346926072821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26017154850251129234763761 19512866137688346926072821)
      ·
        refine ⟨1829331200408282524319327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19512866137688346926072821 1829331200408282524319327)
        ·
          refine ⟨2743996800612423786478991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829331200408282524319327 2743996800612423786478991)
          ·
            refine ⟨4115995200918635679718487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743996800612423786478991 4115995200918635679718487)
            ·
              refine ⟨6173992801377953519577731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115995200918635679718487 6173992801377953519577731)
              ·
                refine ⟨9260989202066930279366597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173992801377953519577731 9260989202066930279366597)
                ·
                  refine ⟨1736435475387549427381237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9260989202066930279366597 1736435475387549427381237)
                  ·
                    refine ⟨162790825817582758816991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1736435475387549427381237 162790825817582758816991)
                    ·
                      rfl

theorem cell22_475551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_475551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475551 prefixEnd_475551 := by exact prefixLift 475551
  have htrace : WordTrace (prefixWord ++ tailWord_475551) baseStart_475551 baseEnd_475551 := by
    simpa [prefixWord, tailWord_475551, baseEnd_475551] using wordTrace_append hprefix tailTrace_475551
  have hstable : (prefixWord ++ tailWord_475551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475551).length < 2 ^ (prefixWord ++ tailWord_475551).sum := by decide
  have hdescent : baseEnd_475551 < baseStart_475551 := by decide
  rcases family_descends (prefixWord ++ tailWord_475551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475634 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_475634 : Nat := 118140960795 + 475634 * 2 ^ 59
def prefixEnd_475634 : Nat := 4983230072969 + 3 ^ 40 * 475634 * 2
def baseEnd_475634 : Nat := 162819238413798208991737

theorem tailTrace_475634 : CollatzResearch.WordTrace tailWord_475634 prefixEnd_475634 162819238413798208991737 := by
  unfold tailWord_475634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336949289716681166278489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11565198105911149776742637 4336949289716681166278489)
  ·
    refine ⟨3252711967287510874708867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336949289716681166278489 3252711967287510874708867)
    ·
      refine ⟨4879067950931266312063301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252711967287510874708867 4879067950931266312063301)
      ·
        refine ⟨914825240799612433511869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4879067950931266312063301 914825240799612433511869)
        ·
          refine ⟨343059465299854662566951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914825240799612433511869 343059465299854662566951)
          ·
            refine ⟨514589197949781993850427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343059465299854662566951 514589197949781993850427)
            ·
              refine ⟨771883796924672990775641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514589197949781993850427 771883796924672990775641)
              ·
                refine ⟨578912847693504743081731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771883796924672990775641 578912847693504743081731)
                ·
                  refine ⟨868369271540257114622597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578912847693504743081731 868369271540257114622597)
                  ·
                    refine ⟨162819238413798208991737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868369271540257114622597 162819238413798208991737)
                    ·
                      rfl

theorem cell22_475634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_475634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475634 prefixEnd_475634 := by exact prefixLift 475634
  have htrace : WordTrace (prefixWord ++ tailWord_475634) baseStart_475634 baseEnd_475634 := by
    simpa [prefixWord, tailWord_475634, baseEnd_475634] using wordTrace_append hprefix tailTrace_475634
  have hstable : (prefixWord ++ tailWord_475634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475634).length < 2 ^ (prefixWord ++ tailWord_475634).sum := by decide
  have hdescent : baseEnd_475634 < baseStart_475634 := by decide
  rcases family_descends (prefixWord ++ tailWord_475634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475641 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_475641 : Nat := 118140960795 + 475641 * 2 ^ 59
def prefixEnd_475641 : Nat := 4983230072969 + 3 ^ 40 * 475641 * 2
def baseEnd_475641 : Nat := 162821634656852524066715

theorem tailTrace_475641 : CollatzResearch.WordTrace tailWord_475641 prefixEnd_475641 162821634656852524066715 := by
  unfold tailWord_475641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348052469841364860618777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11565368313227576573745851 17348052469841364860618777)
  ·
    refine ⟨13011039352381023645464083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17348052469841364860618777 13011039352381023645464083)
    ·
      refine ⟨19516559028571535468196125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011039352381023645464083 19516559028571535468196125)
      ·
        refine ⟨7318709635714325800573547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19516559028571535468196125 7318709635714325800573547)
        ·
          refine ⟨10978064453571488700860321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318709635714325800573547 10978064453571488700860321)
          ·
            refine ⟨8233548340178616525645241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10978064453571488700860321 8233548340178616525645241)
            ·
              refine ⟨6175161255133962394233931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8233548340178616525645241 6175161255133962394233931)
              ·
                refine ⟨9262741882700943591350897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175161255133962394233931 9262741882700943591350897)
                ·
                  refine ⟨6947056412025707693513173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262741882700943591350897 6947056412025707693513173)
                  ·
                    refine ⟨162821634656852524066715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6947056412025707693513173 162821634656852524066715)
                    ·
                      rfl

theorem cell22_475641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_475641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475641 prefixEnd_475641 := by exact prefixLift 475641
  have htrace : WordTrace (prefixWord ++ tailWord_475641) baseStart_475641 baseEnd_475641 := by
    simpa [prefixWord, tailWord_475641, baseEnd_475641] using wordTrace_append hprefix tailTrace_475641
  have hstable : (prefixWord ++ tailWord_475641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475641).length < 2 ^ (prefixWord ++ tailWord_475641).sum := by decide
  have hdescent : baseEnd_475641 < baseStart_475641 := by decide
  rcases family_descends (prefixWord ++ tailWord_475641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475709 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_475709 : Nat := 118140960795 + 475709 * 2 ^ 59
def prefixEnd_475709 : Nat := 4983230072969 + 3 ^ 40 * 475709 * 2
def baseEnd_475709 : Nat := 162844912446523013366507

theorem tailTrace_475709 : CollatzResearch.WordTrace tailWord_475709 prefixEnd_475709 162844912446523013366507 := by
  unfold tailWord_475709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350532633595012474094181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11567021755730008316062787 17350532633595012474094181)
  ·
    refine ⟨3253224868799064838892659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17350532633595012474094181 3253224868799064838892659)
    ·
      refine ⟨4879837303198597258338989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3253224868799064838892659 4879837303198597258338989)
      ·
        refine ⟨1829938988699473971877121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4879837303198597258338989 1829938988699473971877121)
        ·
          refine ⟨1372454241524605478907841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829938988699473971877121 1372454241524605478907841)
          ·
            refine ⟨1029340681143454109180881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372454241524605478907841 1029340681143454109180881)
            ·
              refine ⟨772005510857590581885661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029340681143454109180881 772005510857590581885661)
              ·
                refine ⟨289502066571596468207123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772005510857590581885661 289502066571596468207123)
                ·
                  refine ⟨434253099857394702310685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289502066571596468207123 434253099857394702310685)
                  ·
                    refine ⟨162844912446523013366507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434253099857394702310685 162844912446523013366507)
                    ·
                      rfl

theorem cell22_475709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_475709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475709 prefixEnd_475709 := by exact prefixLift 475709
  have htrace : WordTrace (prefixWord ++ tailWord_475709) baseStart_475709 baseEnd_475709 := by
    simpa [prefixWord, tailWord_475709, baseEnd_475709] using wordTrace_append hprefix tailTrace_475709
  have hstable : (prefixWord ++ tailWord_475709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475709).length < 2 ^ (prefixWord ++ tailWord_475709).sum := by decide
  have hdescent : baseEnd_475709 < baseStart_475709 := by decide
  rcases family_descends (prefixWord ++ tailWord_475709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475733 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 6]
def baseStart_475733 : Nat := 118140960795 + 475733 * 2 ^ 59
def prefixEnd_475733 : Nat := 4983230072969 + 3 ^ 40 * 475733 * 2
def baseEnd_475733 : Nat := 54284376045664983588811

theorem tailTrace_475733 : CollatzResearch.WordTrace tailWord_475733 prefixEnd_475733 54284376045664983588811 := by
  unfold tailWord_475733
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351407985508064572967853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11567605323672043048645235 17351407985508064572967853)
  ·
    refine ⟨6506777994565524214862945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17351407985508064572967853 6506777994565524214862945)
    ·
      refine ⟨4880083495924143161147209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506777994565524214862945 4880083495924143161147209)
      ·
        refine ⟨3660062621943107370860407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880083495924143161147209 3660062621943107370860407)
        ·
          refine ⟨5490093932914661056290611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660062621943107370860407 5490093932914661056290611)
          ·
            refine ⟨8235140899371991584435917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490093932914661056290611 8235140899371991584435917)
            ·
              refine ⟨3088177837264496844163469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8235140899371991584435917 3088177837264496844163469)
              ·
                refine ⟨1158066688974186316561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3088177837264496844163469 1158066688974186316561301)
                ·
                  refine ⟨54284376045664983588811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1158066688974186316561301 54284376045664983588811)
                  ·
                    rfl

theorem cell22_475733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_475733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475733 prefixEnd_475733 := by exact prefixLift 475733
  have htrace : WordTrace (prefixWord ++ tailWord_475733) baseStart_475733 baseEnd_475733 := by
    simpa [prefixWord, tailWord_475733, baseEnd_475733] using wordTrace_append hprefix tailTrace_475733
  have hstable : (prefixWord ++ tailWord_475733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475733).length < 2 ^ (prefixWord ++ tailWord_475733).sum := by decide
  have hdescent : baseEnd_475733 < baseStart_475733 := by decide
  rcases family_descends (prefixWord ++ tailWord_475733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475780 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_475780 : Nat := 118140960795 + 475780 * 2 ^ 59
def prefixEnd_475780 : Nat := 4983230072969 + 3 ^ 40 * 475780 * 2
def baseEnd_475780 : Nat := 162869217197502494841289

theorem tailTrace_475780 : CollatzResearch.WordTrace tailWord_475780 prefixEnd_475780 162869217197502494841289 := by
  unfold tailWord_475780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676561108168895799964397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11568748144225194399952529 8676561108168895799964397)
  ·
    refine ⟨3253710415563335924986649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8676561108168895799964397 3253710415563335924986649)
    ·
      refine ⟨2440282811672501943739987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3253710415563335924986649 2440282811672501943739987)
      ·
        refine ⟨3660424217508752915609981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440282811672501943739987 3660424217508752915609981)
        ·
          refine ⟨1372659081565782343353743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3660424217508752915609981 1372659081565782343353743)
          ·
            refine ⟨2058988622348673515030615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372659081565782343353743 2058988622348673515030615)
            ·
              refine ⟨3088482933523010272545923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058988622348673515030615 3088482933523010272545923)
              ·
                refine ⟨4632724400284515408818885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088482933523010272545923 4632724400284515408818885)
                ·
                  refine ⟨868635825053346639153541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4632724400284515408818885 868635825053346639153541)
                  ·
                    refine ⟨162869217197502494841289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868635825053346639153541 162869217197502494841289)
                    ·
                      rfl

theorem cell22_475780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_475780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475780 prefixEnd_475780 := by exact prefixLift 475780
  have htrace : WordTrace (prefixWord ++ tailWord_475780) baseStart_475780 baseEnd_475780 := by
    simpa [prefixWord, tailWord_475780, baseEnd_475780] using wordTrace_append hprefix tailTrace_475780
  have hstable : (prefixWord ++ tailWord_475780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475780).length < 2 ^ (prefixWord ++ tailWord_475780).sum := by decide
  have hdescent : baseEnd_475780 < baseStart_475780 := by decide
  rcases family_descends (prefixWord ++ tailWord_475780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475840 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_475840 : Nat := 118140960795 + 475840 * 2 ^ 59
def prefixEnd_475840 : Nat := 4983230072969 + 3 ^ 40 * 475840 * 2
def baseEnd_475840 : Nat := 54296585474560779447035

theorem tailTrace_475840 : CollatzResearch.WordTrace tailWord_475840 prefixEnd_475840 54296585474560779447035 := by
  unfold tailWord_475840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677655298060210923556487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11570207064080281231408649 8677655298060210923556487)
  ·
    refine ⟨13016482947090316385334731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677655298060210923556487 13016482947090316385334731)
    ·
      refine ⟨19524724420635474578002097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016482947090316385334731 19524724420635474578002097)
      ·
        refine ⟨14643543315476605933501573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19524724420635474578002097 14643543315476605933501573)
        ·
          refine ⟨2745664371651863612531545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14643543315476605933501573 2745664371651863612531545)
          ·
            refine ⟨2059248278738897709398659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745664371651863612531545 2059248278738897709398659)
            ·
              refine ⟨3088872418108346564097989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059248278738897709398659 3088872418108346564097989)
              ·
                refine ⟨579163578395314980768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3088872418108346564097989 579163578395314980768373)
                ·
                  refine ⟨54296585474560779447035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579163578395314980768373 54296585474560779447035)
                  ·
                    rfl

theorem cell22_475840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_475840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475840 prefixEnd_475840 := by exact prefixLift 475840
  have htrace : WordTrace (prefixWord ++ tailWord_475840) baseStart_475840 baseEnd_475840 := by
    simpa [prefixWord, tailWord_475840, baseEnd_475840] using wordTrace_append hprefix tailTrace_475840
  have hstable : (prefixWord ++ tailWord_475840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475840).length < 2 ^ (prefixWord ++ tailWord_475840).sum := by decide
  have hdescent : baseEnd_475840 < baseStart_475840 := by decide
  rcases family_descends (prefixWord ++ tailWord_475840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475846 : List Nat := [6, 1, 2, 1, 2, 2, 1, 7]
def baseStart_475846 : Nat := 118140960795 + 475846 * 2 ^ 59
def prefixEnd_475846 : Nat := 4983230072969 + 3 ^ 40 * 475846 * 2
def baseEnd_475846 : Nat := 18099090038477813632343

theorem tailTrace_475846 : CollatzResearch.WordTrace tailWord_475846 prefixEnd_475846 18099090038477813632343 := by
  unfold tailWord_475846
  simp only [CollatzResearch.WordTrace]
  refine ⟨542360294815583902244731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11570352956065789914554261 542360294815583902244731)
  ·
    refine ⟨813540442223375853367097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542360294815583902244731 813540442223375853367097)
    ·
      refine ⟨610155331667531890025323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813540442223375853367097 610155331667531890025323)
      ·
        refine ⟨915232997501297835037985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610155331667531890025323 915232997501297835037985)
        ·
          refine ⟨686424748125973376278489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915232997501297835037985 686424748125973376278489)
          ·
            refine ⟨514818561094480032208867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686424748125973376278489 514818561094480032208867)
            ·
              refine ⟨772227841641720048313301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514818561094480032208867 772227841641720048313301)
              ·
                refine ⟨18099090038477813632343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 772227841641720048313301 18099090038477813632343)
                ·
                  rfl

theorem cell22_475846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_475846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475846 prefixEnd_475846 := by exact prefixLift 475846
  have htrace : WordTrace (prefixWord ++ tailWord_475846) baseStart_475846 baseEnd_475846 := by
    simpa [prefixWord, tailWord_475846, baseEnd_475846] using wordTrace_append hprefix tailTrace_475846
  have hstable : (prefixWord ++ tailWord_475846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475846).length < 2 ^ (prefixWord ++ tailWord_475846).sum := by decide
  have hdescent : baseEnd_475846 < baseStart_475846 := by decide
  rcases family_descends (prefixWord ++ tailWord_475846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475885 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 8]
def baseStart_475885 : Nat := 118140960795 + 475885 * 2 ^ 59
def prefixEnd_475885 : Nat := 4983230072969 + 3 ^ 40 * 475885 * 2
def baseEnd_475885 : Nat := 54301720281105740321989

theorem tailTrace_475885 : CollatzResearch.WordTrace tailWord_475885 prefixEnd_475885 54301720281105740321989 := by
  unfold tailWord_475885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356951880957394532501109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11571301253971596355000739 17356951880957394532501109)
  ·
    refine ⟨1627214238839755737421979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17356951880957394532501109 1627214238839755737421979)
    ·
      refine ⟨2440821358259633606132969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627214238839755737421979 2440821358259633606132969)
      ·
        refine ⟨1830616018694725204599727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440821358259633606132969 1830616018694725204599727)
        ·
          refine ⟨2745924028042087806899591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830616018694725204599727 2745924028042087806899591)
          ·
            refine ⟨4118886042063131710349387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745924028042087806899591 4118886042063131710349387)
            ·
              refine ⟨6178329063094697565524081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118886042063131710349387 6178329063094697565524081)
              ·
                refine ⟨4633746797321023174143061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6178329063094697565524081 4633746797321023174143061)
                ·
                  refine ⟨54301720281105740321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4633746797321023174143061 54301720281105740321989)
                  ·
                    rfl

theorem cell22_475885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_475885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475885 prefixEnd_475885 := by exact prefixLift 475885
  have htrace : WordTrace (prefixWord ++ tailWord_475885) baseStart_475885 baseEnd_475885 := by
    simpa [prefixWord, tailWord_475885, baseEnd_475885] using wordTrace_append hprefix tailTrace_475885
  have hstable : (prefixWord ++ tailWord_475885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475885).length < 2 ^ (prefixWord ++ tailWord_475885).sum := by decide
  have hdescent : baseEnd_475885 < baseStart_475885 := by decide
  rcases family_descends (prefixWord ++ tailWord_475885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475887 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 1, 4]
def baseStart_475887 : Nat := 118140960795 + 475887 * 2 ^ 59
def prefixEnd_475887 : Nat := 4983230072969 + 3 ^ 40 * 475887 * 2
def baseEnd_475887 : Nat := 162905845484189882415961

theorem tailTrace_475887 : CollatzResearch.WordTrace tailWord_475887 prefixEnd_475887 162905845484189882415961 := by
  unfold tailWord_475887
  simp only [CollatzResearch.WordTrace]
  refine ⟨17357024826950148874073915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11571349884633432582715943 17357024826950148874073915)
  ·
    refine ⟨26035537240425223311110873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17357024826950148874073915 26035537240425223311110873)
    ·
      refine ⟨19526652930318917483333155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26035537240425223311110873 19526652930318917483333155)
      ·
        refine ⟨29289979395478376224999733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19526652930318917483333155 29289979395478376224999733)
        ·
          refine ⟨2745935568326097771093725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29289979395478376224999733 2745935568326097771093725)
          ·
            refine ⟨1029725838122286664160147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2745935568326097771093725 1029725838122286664160147)
            ·
              refine ⟨1544588757183429996240221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029725838122286664160147 1544588757183429996240221)
              ·
                refine ⟨579220783943786248590083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1544588757183429996240221 579220783943786248590083)
                ·
                  refine ⟨868831175915679372885125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579220783943786248590083 868831175915679372885125)
                  ·
                    refine ⟨162905845484189882415961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868831175915679372885125 162905845484189882415961)
                    ·
                      rfl

theorem cell22_475887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_475887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475887 prefixEnd_475887 := by exact prefixLift 475887
  have htrace : WordTrace (prefixWord ++ tailWord_475887) baseStart_475887 baseEnd_475887 := by
    simpa [prefixWord, tailWord_475887, baseEnd_475887] using wordTrace_append hprefix tailTrace_475887
  have hstable : (prefixWord ++ tailWord_475887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475887).length < 2 ^ (prefixWord ++ tailWord_475887).sum := by decide
  have hdescent : baseEnd_475887 < baseStart_475887 := by decide
  rcases family_descends (prefixWord ++ tailWord_475887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475902 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_475902 : Nat := 118140960795 + 475902 * 2 ^ 59
def prefixEnd_475902 : Nat := 4983230072969 + 3 ^ 40 * 475902 * 2
def baseEnd_475902 : Nat := 54303660096911614430305

theorem tailTrace_475902 : CollatzResearch.WordTrace tailWord_475902 prefixEnd_475902 54303660096911614430305 := by
  unfold tailWord_475902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169696490236975804483745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11571714614597204290579973 2169696490236975804483745)
  ·
    refine ⟨1627272367677731853362809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169696490236975804483745 1627272367677731853362809)
    ·
      refine ⟨1220454275758298890022107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1627272367677731853362809 1220454275758298890022107)
      ·
        refine ⟨1830681413637448335033161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220454275758298890022107 1830681413637448335033161)
        ·
          refine ⟨1373011060228086251274871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830681413637448335033161 1373011060228086251274871)
          ·
            refine ⟨2059516590342129376912307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373011060228086251274871 2059516590342129376912307)
            ·
              refine ⟨3089274885513194065368461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059516590342129376912307 3089274885513194065368461)
              ·
                refine ⟨1158478082067447774513173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3089274885513194065368461 1158478082067447774513173)
                ·
                  refine ⟨54303660096911614430305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1158478082067447774513173 54303660096911614430305)
                  ·
                    rfl

theorem cell22_475902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_475902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475902 prefixEnd_475902 := by exact prefixLift 475902
  have htrace : WordTrace (prefixWord ++ tailWord_475902) baseStart_475902 baseEnd_475902 := by
    simpa [prefixWord, tailWord_475902, baseEnd_475902] using wordTrace_append hprefix tailTrace_475902
  have hstable : (prefixWord ++ tailWord_475902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475902).length < 2 ^ (prefixWord ++ tailWord_475902).sum := by decide
  have hdescent : baseEnd_475902 < baseStart_475902 := by decide
  rcases family_descends (prefixWord ++ tailWord_475902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475930 : List Nat := [3, 1, 1, 3, 2, 1, 3, 8]
def baseStart_475930 : Nat := 118140960795 + 475930 * 2 ^ 59
def prefixEnd_475930 : Nat := 4983230072969 + 3 ^ 40 * 475930 * 2
def baseEnd_475930 : Nat := 18102285029216900398981

theorem tailTrace_475930 : CollatzResearch.WordTrace tailWord_475930 prefixEnd_475930 18102285029216900398981 := by
  unfold tailWord_475930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339648291448591804472311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11572395443862911478592829 4339648291448591804472311)
  ·
    refine ⟨6509472437172887706708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339648291448591804472311 6509472437172887706708467)
    ·
      refine ⟨9764208655759331560062701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509472437172887706708467 9764208655759331560062701)
      ·
        refine ⟨3661578245909749335023513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9764208655759331560062701 3661578245909749335023513)
        ·
          refine ⟨2746183684432312001267635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3661578245909749335023513 2746183684432312001267635)
          ·
            refine ⟨4119275526648468001901453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746183684432312001267635 4119275526648468001901453)
            ·
              refine ⟨1544728322493175500713045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4119275526648468001901453 1544728322493175500713045)
              ·
                refine ⟨18102285029216900398981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1544728322493175500713045 18102285029216900398981)
                ·
                  rfl

theorem cell22_475930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_475930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475930 prefixEnd_475930 := by exact prefixLift 475930
  have htrace : WordTrace (prefixWord ++ tailWord_475930) baseStart_475930 baseEnd_475930 := by
    simpa [prefixWord, tailWord_475930, baseEnd_475930] using wordTrace_append hprefix tailTrace_475930
  have hstable : (prefixWord ++ tailWord_475930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475930).length < 2 ^ (prefixWord ++ tailWord_475930).sum := by decide
  have hdescent : baseEnd_475930 < baseStart_475930 := by decide
  rcases family_descends (prefixWord ++ tailWord_475930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475960 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_475960 : Nat := 118140960795 + 475960 * 2 ^ 59
def prefixEnd_475960 : Nat := 4983230072969 + 3 ^ 40 * 475960 * 2
def baseEnd_475960 : Nat := 162930834876042025340737

theorem tailTrace_475960 : CollatzResearch.WordTrace tailWord_475960 prefixEnd_475960 162930834876042025340737 := by
  unfold tailWord_475960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679843677842841170740667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11573124903790454894320889 8679843677842841170740667)
  ·
    refine ⟨13019765516764261756111001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8679843677842841170740667 13019765516764261756111001)
    ·
      refine ⟨9764824137573196317083251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13019765516764261756111001 9764824137573196317083251)
      ·
        refine ⟨14647236206359794475624877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9764824137573196317083251 14647236206359794475624877)
        ·
          refine ⟨5492713577384922928359329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14647236206359794475624877 5492713577384922928359329)
          ·
            refine ⟨4119535183038692196269497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492713577384922928359329 4119535183038692196269497)
            ·
              refine ⟨3089651387279019147202123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119535183038692196269497 3089651387279019147202123)
              ·
                refine ⟨4634477080918528720803185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089651387279019147202123 4634477080918528720803185)
                ·
                  refine ⟨3475857810688896540602389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4634477080918528720803185 3475857810688896540602389)
                  ·
                    refine ⟨162930834876042025340737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3475857810688896540602389 162930834876042025340737)
                    ·
                      rfl

theorem cell22_475960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_475960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_475960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_475960 prefixEnd_475960 := by exact prefixLift 475960
  have htrace : WordTrace (prefixWord ++ tailWord_475960) baseStart_475960 baseEnd_475960 := by
    simpa [prefixWord, tailWord_475960, baseEnd_475960] using wordTrace_append hprefix tailTrace_475960
  have hstable : (prefixWord ++ tailWord_475960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475960).length < 2 ^ (prefixWord ++ tailWord_475960).sum := by decide
  have hdescent : baseEnd_475960 < baseStart_475960 := by decide
  rcases family_descends (prefixWord ++ tailWord_475960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476037 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 6]
def baseStart_476037 : Nat := 118140960795 + 476037 * 2 ^ 59
def prefixEnd_476037 : Nat := 4983230072969 + 3 ^ 40 * 476037 * 2
def baseEnd_476037 : Nat := 54319064516546497055167

theorem tailTrace_476037 : CollatzResearch.WordTrace tailWord_476037 prefixEnd_476037 54319064516546497055167 := by
  unfold tailWord_476037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17362495776406724492034365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11574997184271149661356243 17362495776406724492034365)
  ·
    refine ⟨6510935916152521684512887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17362495776406724492034365 6510935916152521684512887)
    ·
      refine ⟨9766403874228782526769331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510935916152521684512887 9766403874228782526769331)
      ·
        refine ⟨14649605811343173790153997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766403874228782526769331 14649605811343173790153997)
        ·
          refine ⟨5493602179253690171307749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14649605811343173790153997 5493602179253690171307749)
          ·
            refine ⟨1030050408610066907120203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5493602179253690171307749 1030050408610066907120203)
            ·
              refine ⟨1545075612915100360680305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030050408610066907120203 1545075612915100360680305)
              ·
                refine ⟨1158806709686325270510229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545075612915100360680305 1158806709686325270510229)
                ·
                  refine ⟨54319064516546497055167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1158806709686325270510229 54319064516546497055167)
                  ·
                    rfl

theorem cell22_476037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_476037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476037 prefixEnd_476037 := by exact prefixLift 476037
  have htrace : WordTrace (prefixWord ++ tailWord_476037) baseStart_476037 baseEnd_476037 := by
    simpa [prefixWord, tailWord_476037, baseEnd_476037] using wordTrace_append hprefix tailTrace_476037
  have hstable : (prefixWord ++ tailWord_476037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476037).length < 2 ^ (prefixWord ++ tailWord_476037).sum := by decide
  have hdescent : baseEnd_476037 < baseStart_476037 := by decide
  rcases family_descends (prefixWord ++ tailWord_476037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476067 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_476067 : Nat := 118140960795 + 476067 * 2 ^ 59
def prefixEnd_476067 : Nat := 4983230072969 + 3 ^ 40 * 476067 * 2
def baseEnd_476067 : Nat := 162967463162729412915409

theorem tailTrace_476067 : CollatzResearch.WordTrace tailWord_476067 prefixEnd_476067 162967463162729412915409 := by
  unfold tailWord_476067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17363589966298039615626455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11575726644198693077084303 17363589966298039615626455)
  ·
    refine ⟨26045384949447059423439683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17363589966298039615626455 26045384949447059423439683)
    ·
      refine ⟨39068077424170589135159525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26045384949447059423439683 39068077424170589135159525)
      ·
        refine ⟨7325264517031985462842411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39068077424170589135159525 7325264517031985462842411)
        ·
          refine ⟨10987896775547978194263617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325264517031985462842411 10987896775547978194263617)
          ·
            refine ⟨8240922581660983645697713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10987896775547978194263617 8240922581660983645697713)
            ·
              refine ⟨6180691936245737734273285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240922581660983645697713 6180691936245737734273285)
              ·
                refine ⟨1158879738046075825176241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6180691936245737734273285 1158879738046075825176241)
                ·
                  refine ⟨869159803534556868882181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158879738046075825176241 869159803534556868882181)
                  ·
                    refine ⟨162967463162729412915409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869159803534556868882181 162967463162729412915409)
                    ·
                      rfl

theorem cell22_476067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_476067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476067 prefixEnd_476067 := by exact prefixLift 476067
  have htrace : WordTrace (prefixWord ++ tailWord_476067) baseStart_476067 baseEnd_476067 := by
    simpa [prefixWord, tailWord_476067, baseEnd_476067] using wordTrace_append hprefix tailTrace_476067
  have hstable : (prefixWord ++ tailWord_476067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476067).length < 2 ^ (prefixWord ++ tailWord_476067).sum := by decide
  have hdescent : baseEnd_476067 < baseStart_476067 := by decide
  rcases family_descends (prefixWord ++ tailWord_476067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476204 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_476204 : Nat := 118140960795 + 476204 * 2 ^ 59
def prefixEnd_476204 : Nat := 4983230072969 + 3 ^ 40 * 476204 * 2
def baseEnd_476204 : Nat := 163014361062506722239989

theorem tailTrace_476204 : CollatzResearch.WordTrace tailWord_476204 prefixEnd_476204 163014361062506722239989 := by
  unfold tailWord_476204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684293383400856006681833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11579057844534474675575777 8684293383400856006681833)
  ·
    refine ⟨6513220037550642005011375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8684293383400856006681833 6513220037550642005011375)
    ·
      refine ⟨9769830056325963007517063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6513220037550642005011375 9769830056325963007517063)
      ·
        refine ⟨14654745084488944511275595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769830056325963007517063 14654745084488944511275595)
        ·
          refine ⟨21982117626733416766913393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654745084488944511275595 21982117626733416766913393)
          ·
            refine ⟨16486588220050062575185045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21982117626733416766913393 16486588220050062575185045)
            ·
              refine ⟨772808822814846683211799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16486588220050062575185045 772808822814846683211799)
              ·
                refine ⟨1159213234222270024817699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772808822814846683211799 1159213234222270024817699)
                ·
                  refine ⟨1738819851333405037226549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159213234222270024817699 1738819851333405037226549)
                  ·
                    refine ⟨163014361062506722239989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1738819851333405037226549 163014361062506722239989)
                    ·
                      rfl

theorem cell22_476204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_476204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476204 prefixEnd_476204 := by exact prefixLift 476204
  have htrace : WordTrace (prefixWord ++ tailWord_476204) baseStart_476204 baseEnd_476204 := by
    simpa [prefixWord, tailWord_476204, baseEnd_476204] using wordTrace_append hprefix tailTrace_476204
  have hstable : (prefixWord ++ tailWord_476204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476204).length < 2 ^ (prefixWord ++ tailWord_476204).sum := by decide
  have hdescent : baseEnd_476204 < baseStart_476204 := by decide
  rcases family_descends (prefixWord ++ tailWord_476204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476225 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_476225 : Nat := 118140960795 + 476225 * 2 ^ 59
def prefixEnd_476225 : Nat := 4983230072969 + 3 ^ 40 * 476225 * 2
def baseEnd_476225 : Nat := 163021549791669667464925

theorem tailTrace_476225 : CollatzResearch.WordTrace tailWord_476225 prefixEnd_476225 163021549791669667464925 := by
  unfold tailWord_476225
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369352699725632599878129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11579568466483755066585419 17369352699725632599878129)
  ·
    refine ⟨13027014524794224449908597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17369352699725632599878129 13027014524794224449908597)
    ·
      refine ⟨1221282611699458542178931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13027014524794224449908597 1221282611699458542178931)
      ·
        refine ⟨1831923917549187813268397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221282611699458542178931 1831923917549187813268397)
        ·
          refine ⟨686971469080945429975649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1831923917549187813268397 686971469080945429975649)
          ·
            refine ⟨515228601810709072481737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686971469080945429975649 515228601810709072481737)
            ·
              refine ⟨386421451358031804361303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515228601810709072481737 386421451358031804361303)
              ·
                refine ⟨579632177037047706541955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386421451358031804361303 579632177037047706541955)
                ·
                  refine ⟨869448265555571559812933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579632177037047706541955 869448265555571559812933)
                  ·
                    refine ⟨163021549791669667464925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869448265555571559812933 163021549791669667464925)
                    ·
                      rfl

theorem cell22_476225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_476225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476225 prefixEnd_476225 := by exact prefixLift 476225
  have htrace : WordTrace (prefixWord ++ tailWord_476225) baseStart_476225 baseEnd_476225 := by
    simpa [prefixWord, tailWord_476225, baseEnd_476225] using wordTrace_append hprefix tailTrace_476225
  have hstable : (prefixWord ++ tailWord_476225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476225).length < 2 ^ (prefixWord ++ tailWord_476225).sum := by decide
  have hdescent : baseEnd_476225 < baseStart_476225 := by decide
  rcases family_descends (prefixWord ++ tailWord_476225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476339 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_476339 : Nat := 118140960795 + 476339 * 2 ^ 59
def prefixEnd_476339 : Nat := 4983230072969 + 3 ^ 40 * 476339 * 2
def baseEnd_476339 : Nat := 163060574321411370114575

theorem tailTrace_476339 : CollatzResearch.WordTrace tailWord_476339 prefixEnd_476339 163060574321411370114575 := by
  unfold tailWord_476339
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373510621312630069528071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11582340414208420046352047 17373510621312630069528071)
  ·
    refine ⟨26060265931968945104292107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17373510621312630069528071 26060265931968945104292107)
    ·
      refine ⟨39090398897953417656438161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26060265931968945104292107 39090398897953417656438161)
      ·
        refine ⟨29317799173465063242328621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39090398897953417656438161 29317799173465063242328621)
        ·
          refine ⟨10994174690049398715873233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29317799173465063242328621 10994174690049398715873233)
          ·
            refine ⟨8245631017537049036904925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994174690049398715873233 8245631017537049036904925)
            ·
              refine ⟨3092111631576393388839347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8245631017537049036904925 3092111631576393388839347)
              ·
                refine ⟨4638167447364590083259021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092111631576393388839347 4638167447364590083259021)
                ·
                  refine ⟨1739312792761721281222133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4638167447364590083259021 1739312792761721281222133)
                  ·
                    refine ⟨163060574321411370114575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1739312792761721281222133 163060574321411370114575)
                    ·
                      rfl

theorem cell22_476339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_476339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476339 prefixEnd_476339 := by exact prefixLift 476339
  have htrace : WordTrace (prefixWord ++ tailWord_476339) baseStart_476339 baseEnd_476339 := by
    simpa [prefixWord, tailWord_476339, baseEnd_476339] using wordTrace_append hprefix tailTrace_476339
  have hstable : (prefixWord ++ tailWord_476339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476339).length < 2 ^ (prefixWord ++ tailWord_476339).sum := by decide
  have hdescent : baseEnd_476339 < baseStart_476339 := by decide
  rcases family_descends (prefixWord ++ tailWord_476339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476343 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 1, 4]
def baseStart_476343 : Nat := 118140960795 + 476343 * 2 ^ 59
def prefixEnd_476343 : Nat := 4983230072969 + 3 ^ 40 * 476343 * 2
def baseEnd_476343 : Nat := 163061943603156693014563

theorem tailTrace_476343 : CollatzResearch.WordTrace tailWord_476343 prefixEnd_476343 163061943603156693014563 := by
  unfold tailWord_476343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373656513298138752673683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11582437675532092501782455 17373656513298138752673683)
  ·
    refine ⟨26060484769947208129010525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17373656513298138752673683 26060484769947208129010525)
    ·
      refine ⟨9772681788730203048378947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26060484769947208129010525 9772681788730203048378947)
      ·
        refine ⟨14659022683095304572568421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772681788730203048378947 14659022683095304572568421)
        ·
          refine ⟨2748566753080369607356579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14659022683095304572568421 2748566753080369607356579)
          ·
            refine ⟨4122850129620554411034869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748566753080369607356579 4122850129620554411034869)
            ·
              refine ⟨386517199651926976034519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4122850129620554411034869 386517199651926976034519)
              ·
                refine ⟨579775799477890464051779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386517199651926976034519 579775799477890464051779)
                ·
                  refine ⟨869663699216835696077669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579775799477890464051779 869663699216835696077669)
                  ·
                    refine ⟨163061943603156693014563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869663699216835696077669 163061943603156693014563)
                    ·
                      rfl

theorem cell22_476343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_476343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476343 prefixEnd_476343 := by exact prefixLift 476343
  have htrace : WordTrace (prefixWord ++ tailWord_476343) baseStart_476343 baseEnd_476343 := by
    simpa [prefixWord, tailWord_476343, baseEnd_476343] using wordTrace_append hprefix tailTrace_476343
  have hstable : (prefixWord ++ tailWord_476343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476343).length < 2 ^ (prefixWord ++ tailWord_476343).sum := by decide
  have hdescent : baseEnd_476343 < baseStart_476343 := by decide
  rcases family_descends (prefixWord ++ tailWord_476343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476373 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_476373 : Nat := 118140960795 + 476373 * 2 ^ 59
def prefixEnd_476373 : Nat := 4983230072969 + 3 ^ 40 * 476373 * 2
def baseEnd_476373 : Nat := 163072213216246614764471

theorem tailTrace_476373 : CollatzResearch.WordTrace tailWord_476373 prefixEnd_476373 163072213216246614764471 := by
  unfold tailWord_476373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17374750703189453876265773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11583167135459635917510515 17374750703189453876265773)
  ·
    refine ⟨6515531513696045203599665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17374750703189453876265773 6515531513696045203599665)
    ·
      refine ⟨4886648635272033902699749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6515531513696045203599665 4886648635272033902699749)
      ·
        refine ⟨916246619113506356756203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4886648635272033902699749 916246619113506356756203)
        ·
          refine ⟨1374369928670259535134305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916246619113506356756203 1374369928670259535134305)
          ·
            refine ⟨1030777446502694651350729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374369928670259535134305 1030777446502694651350729)
            ·
              refine ⟨773083084877020988513047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030777446502694651350729 773083084877020988513047)
              ·
                refine ⟨1159624627315531482769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773083084877020988513047 1159624627315531482769571)
                ·
                  refine ⟨1739436940973297224154357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159624627315531482769571 1739436940973297224154357)
                  ·
                    refine ⟨163072213216246614764471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1739436940973297224154357 163072213216246614764471)
                    ·
                      rfl

theorem cell22_476373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_476373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476373 prefixEnd_476373 := by exact prefixLift 476373
  have htrace : WordTrace (prefixWord ++ tailWord_476373) baseStart_476373 baseEnd_476373 := by
    simpa [prefixWord, tailWord_476373, baseEnd_476373] using wordTrace_append hprefix tailTrace_476373
  have hstable : (prefixWord ++ tailWord_476373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476373).length < 2 ^ (prefixWord ++ tailWord_476373).sum := by decide
  have hdescent : baseEnd_476373 < baseStart_476373 := by decide
  rcases family_descends (prefixWord ++ tailWord_476373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476401 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_476401 : Nat := 118140960795 + 476401 * 2 ^ 59
def prefixEnd_476401 : Nat := 4983230072969 + 3 ^ 40 * 476401 * 2
def baseEnd_476401 : Nat := 163081798188463875064385

theorem tailTrace_476401 : CollatzResearch.WordTrace tailWord_476401 prefixEnd_476401 163081798188463875064385 := by
  unfold tailWord_476401
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375771947088014658285057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11583847964725343105523371 17375771947088014658285057)
  ·
    refine ⟨13031828960316010993713793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17375771947088014658285057 13031828960316010993713793)
    ·
      refine ⟨9773871720237008245285345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13031828960316010993713793 9773871720237008245285345)
      ·
        refine ⟨7330403790177756183964009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9773871720237008245285345 7330403790177756183964009)
        ·
          refine ⟨5497802842633317137973007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7330403790177756183964009 5497802842633317137973007)
          ·
            refine ⟨8246704263949975706959511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497802842633317137973007 8246704263949975706959511)
            ·
              refine ⟨12370056395924963560439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246704263949975706959511 12370056395924963560439267)
              ·
                refine ⟨18555084593887445340658901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370056395924963560439267 18555084593887445340658901)
                ·
                  refine ⟨434884795169237000171693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18555084593887445340658901 434884795169237000171693)
                  ·
                    refine ⟨163081798188463875064385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434884795169237000171693 163081798188463875064385)
                    ·
                      rfl

theorem cell22_476401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_476401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476401 prefixEnd_476401 := by exact prefixLift 476401
  have htrace : WordTrace (prefixWord ++ tailWord_476401) baseStart_476401 baseEnd_476401 := by
    simpa [prefixWord, tailWord_476401, baseEnd_476401] using wordTrace_append hprefix tailTrace_476401
  have hstable : (prefixWord ++ tailWord_476401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476401).length < 2 ^ (prefixWord ++ tailWord_476401).sum := by decide
  have hdescent : baseEnd_476401 < baseStart_476401 := by decide
  rcases family_descends (prefixWord ++ tailWord_476401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476478 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_476478 : Nat := 118140960795 + 476478 * 2 ^ 59
def prefixEnd_476478 : Nat := 4983230072969 + 3 ^ 40 * 476478 * 2
def baseEnd_476478 : Nat := 163108156862061340889149

theorem tailTrace_476478 : CollatzResearch.WordTrace tailWord_476478 prefixEnd_476478 163108156862061340889149 := by
  unfold tailWord_476478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172322545976132101104761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11585720245206037872558725 2172322545976132101104761)
  ·
    refine ⟨1629241909482099075828571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2172322545976132101104761 1629241909482099075828571)
    ·
      refine ⟨2443862864223148613742857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629241909482099075828571 2443862864223148613742857)
      ·
        refine ⟨1832897148167361460307143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2443862864223148613742857 1832897148167361460307143)
        ·
          refine ⟨2749345722251042190460715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832897148167361460307143 2749345722251042190460715)
          ·
            refine ⟨4124018583376563285691073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749345722251042190460715 4124018583376563285691073)
            ·
              refine ⟨3093013937532422464268305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124018583376563285691073 3093013937532422464268305)
              ·
                refine ⟨2319760453149316848201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093013937532422464268305 2319760453149316848201229)
                ·
                  refine ⟨869910169930993818075461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319760453149316848201229 869910169930993818075461)
                  ·
                    refine ⟨163108156862061340889149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869910169930993818075461 163108156862061340889149)
                    ·
                      rfl

theorem cell22_476478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_476478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476478 prefixEnd_476478 := by exact prefixLift 476478
  have htrace : WordTrace (prefixWord ++ tailWord_476478) baseStart_476478 baseEnd_476478 := by
    simpa [prefixWord, tailWord_476478, baseEnd_476478] using wordTrace_append hprefix tailTrace_476478
  have hstable : (prefixWord ++ tailWord_476478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476478).length < 2 ^ (prefixWord ++ tailWord_476478).sum := by decide
  have hdescent : baseEnd_476478 < baseStart_476478 := by decide
  rcases family_descends (prefixWord ++ tailWord_476478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476506 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_476506 : Nat := 118140960795 + 476506 * 2 ^ 59
def prefixEnd_476506 : Nat := 4983230072969 + 3 ^ 40 * 476506 * 2
def baseEnd_476506 : Nat := 163117741834278601189063

theorem tailTrace_476506 : CollatzResearch.WordTrace tailWord_476506 prefixEnd_476506 163117741834278601189063 := by
  unfold tailWord_476506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344900402926904397714343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11586401074471745060571581 4344900402926904397714343)
  ·
    refine ⟨6517350604390356596571515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344900402926904397714343 6517350604390356596571515)
    ·
      refine ⟨9776025906585534894857273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6517350604390356596571515 9776025906585534894857273)
      ·
        refine ⟨7332019429939151171142955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776025906585534894857273 7332019429939151171142955)
        ·
          refine ⟨10998029144908726756714433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332019429939151171142955 10998029144908726756714433)
          ·
            refine ⟨8248521858681545067535825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998029144908726756714433 8248521858681545067535825)
            ·
              refine ⟨6186391394011158800651869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248521858681545067535825 6186391394011158800651869)
              ·
                refine ⟨2319896772754184550244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186391394011158800651869 2319896772754184550244451)
                ·
                  refine ⟨3479845159131276825366677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319896772754184550244451 3479845159131276825366677)
                  ·
                    refine ⟨163117741834278601189063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3479845159131276825366677 163117741834278601189063)
                    ·
                      rfl

theorem cell22_476506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_476506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476506 prefixEnd_476506 := by exact prefixLift 476506
  have htrace : WordTrace (prefixWord ++ tailWord_476506) baseStart_476506 baseEnd_476506 := by
    simpa [prefixWord, tailWord_476506, baseEnd_476506] using wordTrace_append hprefix tailTrace_476506
  have hstable : (prefixWord ++ tailWord_476506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476506).length < 2 ^ (prefixWord ++ tailWord_476506).sum := by decide
  have hdescent : baseEnd_476506 < baseStart_476506 := by decide
  rcases family_descends (prefixWord ++ tailWord_476506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476525 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_476525 : Nat := 118140960795 + 476525 * 2 ^ 59
def prefixEnd_476525 : Nat := 4983230072969 + 3 ^ 40 * 476525 * 2
def baseEnd_476525 : Nat := 163124245922568884964005

theorem tailTrace_476525 : CollatzResearch.WordTrace tailWord_476525 prefixEnd_476525 163124245922568884964005 := by
  unfold tailWord_476525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380294598638783835799029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586863065759189223866019 17380294598638783835799029)
  ·
    refine ⟨1629402618622385984606159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17380294598638783835799029 1629402618622385984606159)
    ·
      refine ⟨2444103927933578976909239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629402618622385984606159 2444103927933578976909239)
      ·
        refine ⟨3666155891900368465363859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444103927933578976909239 3666155891900368465363859)
        ·
          refine ⟨5499233837850552698045789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666155891900368465363859 5499233837850552698045789)
          ·
            refine ⟨2062212689193957261767171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499233837850552698045789 2062212689193957261767171)
            ·
              refine ⟨3093319033790935892650757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062212689193957261767171 3093319033790935892650757)
              ·
                refine ⟨579997318835800479872017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3093319033790935892650757 579997318835800479872017)
                ·
                  refine ⟨434997989126850359904013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579997318835800479872017 434997989126850359904013)
                  ·
                    refine ⟨163124245922568884964005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434997989126850359904013 163124245922568884964005)
                    ·
                      rfl

theorem cell22_476525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_476525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476525 prefixEnd_476525 := by exact prefixLift 476525
  have htrace : WordTrace (prefixWord ++ tailWord_476525) baseStart_476525 baseEnd_476525 := by
    simpa [prefixWord, tailWord_476525, baseEnd_476525] using wordTrace_append hprefix tailTrace_476525
  have hstable : (prefixWord ++ tailWord_476525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476525).length < 2 ^ (prefixWord ++ tailWord_476525).sum := by decide
  have hdescent : baseEnd_476525 < baseStart_476525 := by decide
  rcases family_descends (prefixWord ++ tailWord_476525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476583 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 7]
def baseStart_476583 : Nat := 118140960795 + 476583 * 2 ^ 59
def prefixEnd_476583 : Nat := 4983230072969 + 3 ^ 40 * 476583 * 2
def baseEnd_476583 : Nat := 54381366835958689004609

theorem tailTrace_476583 : CollatzResearch.WordTrace tailWord_476583 prefixEnd_476583 54381366835958689004609 := by
  unfold tailWord_476583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17382410032428659741410403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11588273354952439827606935 17382410032428659741410403)
  ·
    refine ⟨26073615048642989612115605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17382410032428659741410403 26073615048642989612115605)
    ·
      refine ⟨1222200705405140138067919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26073615048642989612115605 1222200705405140138067919)
      ·
        refine ⟨1833301058107710207101879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222200705405140138067919 1833301058107710207101879)
        ·
          refine ⟨2749951587161565310652819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833301058107710207101879 2749951587161565310652819)
          ·
            refine ⟨4124927380742347965979229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749951587161565310652819 4124927380742347965979229)
            ·
              refine ⟨1546847767778380487242211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4124927380742347965979229 1546847767778380487242211)
              ·
                refine ⟨2320271651667570730863317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546847767778380487242211 2320271651667570730863317)
                ·
                  refine ⟨54381366835958689004609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2320271651667570730863317 54381366835958689004609)
                  ·
                    rfl

theorem cell22_476583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_476583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476583 prefixEnd_476583 := by exact prefixLift 476583
  have htrace : WordTrace (prefixWord ++ tailWord_476583) baseStart_476583 baseEnd_476583 := by
    simpa [prefixWord, tailWord_476583, baseEnd_476583] using wordTrace_append hprefix tailTrace_476583
  have hstable : (prefixWord ++ tailWord_476583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476583).length < 2 ^ (prefixWord ++ tailWord_476583).sum := by decide
  have hdescent : baseEnd_476583 < baseStart_476583 := by decide
  rcases family_descends (prefixWord ++ tailWord_476583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476645 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 6]
def baseStart_476645 : Nat := 118140960795 + 476645 * 2 ^ 59
def prefixEnd_476645 : Nat := 4983230072969 + 3 ^ 40 * 476645 * 2
def baseEnd_476645 : Nat := 54388441458309523987879

theorem tailTrace_476645 : CollatzResearch.WordTrace tailWord_476645 prefixEnd_476645 54388441458309523987879 := by
  unfold tailWord_476645
  simp only [CollatzResearch.WordTrace]
  refine ⟨17384671358204044330167389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11589780905469362886778259 17384671358204044330167389)
  ·
    refine ⟨6519251759326516623812771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17384671358204044330167389 6519251759326516623812771)
    ·
      refine ⟨9778877638989774935719157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6519251759326516623812771 9778877638989774935719157)
      ·
        refine ⟨916769778655291400223671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9778877638989774935719157 916769778655291400223671)
        ·
          refine ⟨1375154667982937100335507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916769778655291400223671 1375154667982937100335507)
          ·
            refine ⟨2062732001974405650503261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375154667982937100335507 2062732001974405650503261)
            ·
              refine ⟨773524500740402118938723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2062732001974405650503261 773524500740402118938723)
              ·
                refine ⟨1160286751110603178408085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773524500740402118938723 1160286751110603178408085)
                ·
                  refine ⟨54388441458309523987879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1160286751110603178408085 54388441458309523987879)
                  ·
                    rfl

theorem cell22_476645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_476645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476645 prefixEnd_476645 := by exact prefixLift 476645
  have htrace : WordTrace (prefixWord ++ tailWord_476645) baseStart_476645 baseEnd_476645 := by
    simpa [prefixWord, tailWord_476645, baseEnd_476645] using wordTrace_append hprefix tailTrace_476645
  have hstable : (prefixWord ++ tailWord_476645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476645).length < 2 ^ (prefixWord ++ tailWord_476645).sum := by decide
  have hdescent : baseEnd_476645 < baseStart_476645 := by decide
  rcases family_descends (prefixWord ++ tailWord_476645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476696 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_476696 : Nat := 118140960795 + 476696 * 2 ^ 59
def prefixEnd_476696 : Nat := 4983230072969 + 3 ^ 40 * 476696 * 2
def baseEnd_476696 : Nat := 54394260905727146312827

theorem tailTrace_476696 : CollatzResearch.WordTrace tailWord_476696 prefixEnd_476696 54394260905727146312827 := by
  unfold tailWord_476696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693265740509640020136971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11591020987346186693515961 8693265740509640020136971)
  ·
    refine ⟨13039898610764460030205457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8693265740509640020136971 13039898610764460030205457)
    ·
      refine ⟨9779923958073345022654093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13039898610764460030205457 9779923958073345022654093)
      ·
        refine ⟨3667471484277504383495285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9779923958073345022654093 3667471484277504383495285)
        ·
          refine ⟨343825451651016035952683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3667471484277504383495285 343825451651016035952683)
          ·
            refine ⟨515738177476524053929025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343825451651016035952683 515738177476524053929025)
            ·
              refine ⟨386803633107393040446769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515738177476524053929025 386803633107393040446769)
              ·
                refine ⟨290102724830544780335077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386803633107393040446769 290102724830544780335077)
                ·
                  refine ⟨54394260905727146312827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290102724830544780335077 54394260905727146312827)
                  ·
                    rfl

theorem cell22_476696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_476696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476696 prefixEnd_476696 := by exact prefixLift 476696
  have htrace : WordTrace (prefixWord ++ tailWord_476696) baseStart_476696 baseEnd_476696 := by
    simpa [prefixWord, tailWord_476696, baseEnd_476696] using wordTrace_append hprefix tailTrace_476696
  have hstable : (prefixWord ++ tailWord_476696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476696).length < 2 ^ (prefixWord ++ tailWord_476696).sum := by decide
  have hdescent : baseEnd_476696 < baseStart_476696 := by decide
  rcases family_descends (prefixWord ++ tailWord_476696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476703 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_476703 : Nat := 118140960795 + 476703 * 2 ^ 59
def prefixEnd_476703 : Nat := 4983230072969 + 3 ^ 40 * 476703 * 2
def baseEnd_476703 : Nat := 163185178960235754013459

theorem tailTrace_476703 : CollatzResearch.WordTrace tailWord_476703 prefixEnd_476703 163185178960235754013459 := by
  unfold tailWord_476703
  simp only [CollatzResearch.WordTrace]
  refine ⟨17386786791993920235778763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11591191194662613490519175 17386786791993920235778763)
  ·
    refine ⟨26080180187990880353668145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17386786791993920235778763 26080180187990880353668145)
    ·
      refine ⟨19560135140993160265251109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26080180187990880353668145 19560135140993160265251109)
      ·
        refine ⟨3667525338936217549734583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19560135140993160265251109 3667525338936217549734583)
        ·
          refine ⟨5501288008404326324601875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667525338936217549734583 5501288008404326324601875)
          ·
            refine ⟨8251932012606489486902813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501288008404326324601875 8251932012606489486902813)
            ·
              refine ⟨3094474504727433557588555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8251932012606489486902813 3094474504727433557588555)
              ·
                refine ⟨4641711757091150336382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094474504727433557588555 4641711757091150336382833)
                ·
                  refine ⟨3481283817818362752287125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641711757091150336382833 3481283817818362752287125)
                  ·
                    refine ⟨163185178960235754013459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3481283817818362752287125 163185178960235754013459)
                    ·
                      rfl

theorem cell22_476703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_476703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476703 prefixEnd_476703 := by exact prefixLift 476703
  have htrace : WordTrace (prefixWord ++ tailWord_476703) baseStart_476703 baseEnd_476703 := by
    simpa [prefixWord, tailWord_476703, baseEnd_476703] using wordTrace_append hprefix tailTrace_476703
  have hstable : (prefixWord ++ tailWord_476703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476703).length < 2 ^ (prefixWord ++ tailWord_476703).sum := by decide
  have hdescent : baseEnd_476703 < baseStart_476703 := by decide
  rcases family_descends (prefixWord ++ tailWord_476703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476707 : List Nat := [1, 1, 1, 4, 6, 1, 1, 7]
def baseStart_476707 : Nat := 118140960795 + 476707 * 2 ^ 59
def prefixEnd_476707 : Nat := 4983230072969 + 3 ^ 40 * 476707 * 2
def baseEnd_476707 : Nat := 18131838693553452990383

theorem tailTrace_476707 : CollatzResearch.WordTrace tailWord_476707 prefixEnd_476707 18131838693553452990383 := by
  unfold tailWord_476707
  simp only [CollatzResearch.WordTrace]
  refine ⟨17386932683979428918924375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11591288455986285945949583 17386932683979428918924375)
  ·
    refine ⟨26080399025969143378386563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17386932683979428918924375 26080399025969143378386563)
    ·
      refine ⟨39120598538953715067579845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26080399025969143378386563 39120598538953715067579845)
      ·
        refine ⟨7335112226053821575171221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39120598538953715067579845 7335112226053821575171221)
        ·
          refine ⟨343833385596272886336151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7335112226053821575171221 343833385596272886336151)
          ·
            refine ⟨515750078394409329504227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343833385596272886336151 515750078394409329504227)
            ·
              refine ⟨773625117591613994256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515750078394409329504227 773625117591613994256341)
              ·
                refine ⟨18131838693553452990383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773625117591613994256341 18131838693553452990383)
                ·
                  rfl

theorem cell22_476707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 7].length) (baseStart_476707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476707 prefixEnd_476707 := by exact prefixLift 476707
  have htrace : WordTrace (prefixWord ++ tailWord_476707) baseStart_476707 baseEnd_476707 := by
    simpa [prefixWord, tailWord_476707, baseEnd_476707] using wordTrace_append hprefix tailTrace_476707
  have hstable : (prefixWord ++ tailWord_476707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476707).length < 2 ^ (prefixWord ++ tailWord_476707).sum := by decide
  have hdescent : baseEnd_476707 < baseStart_476707 := by decide
  rcases family_descends (prefixWord ++ tailWord_476707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476726 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_476726 : Nat := 118140960795 + 476726 * 2 ^ 59
def prefixEnd_476726 : Nat := 4983230072969 + 3 ^ 40 * 476726 * 2
def baseEnd_476726 : Nat := 163193052330271360688389

theorem tailTrace_476726 : CollatzResearch.WordTrace tailWord_476726 prefixEnd_476726 163193052330271360688389 := by
  unfold tailWord_476726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086726604431912197741627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11591750447273730109244021 1086726604431912197741627)
  ·
    refine ⟨1630089906647868296612441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086726604431912197741627 1630089906647868296612441)
    ·
      refine ⟨1222567429985901222459331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1630089906647868296612441 1222567429985901222459331)
      ·
        refine ⟨1833851144978851833688997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222567429985901222459331 1833851144978851833688997)
        ·
          refine ⟨343847089683534718816687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1833851144978851833688997 343847089683534718816687)
          ·
            refine ⟨515770634525302078225031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343847089683534718816687 515770634525302078225031)
            ·
              refine ⟨773655951787953117337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515770634525302078225031 773655951787953117337547)
              ·
                refine ⟨1160483927681929676006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773655951787953117337547 1160483927681929676006321)
                ·
                  refine ⟨870362945761447257004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160483927681929676006321 870362945761447257004741)
                  ·
                    refine ⟨163193052330271360688389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870362945761447257004741 163193052330271360688389)
                    ·
                      rfl

theorem cell22_476726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_476726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476726 prefixEnd_476726 := by exact prefixLift 476726
  have htrace : WordTrace (prefixWord ++ tailWord_476726) baseStart_476726 baseEnd_476726 := by
    simpa [prefixWord, tailWord_476726, baseEnd_476726] using wordTrace_append hprefix tailTrace_476726
  have hstable : (prefixWord ++ tailWord_476726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476726).length < 2 ^ (prefixWord ++ tailWord_476726).sum := by decide
  have hdescent : baseEnd_476726 < baseStart_476726 := by decide
  rcases family_descends (prefixWord ++ tailWord_476726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476795 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 6, 3]
def baseStart_476795 : Nat := 118140960795 + 476795 * 2 ^ 59
def prefixEnd_476795 : Nat := 4983230072969 + 3 ^ 40 * 476795 * 2
def baseEnd_476795 : Nat := 163216672440378180713177

theorem tailTrace_476795 : CollatzResearch.WordTrace tailWord_476795 prefixEnd_476795 163216672440378180713177 := by
  unfold tailWord_476795
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390142307660619948127839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11593428205107079965418559 17390142307660619948127839)
  ·
    refine ⟨26085213461490929922191759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17390142307660619948127839 26085213461490929922191759)
    ·
      refine ⟨39127820192236394883287639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26085213461490929922191759 39127820192236394883287639)
      ·
        refine ⟨58691730288354592324931459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39127820192236394883287639 58691730288354592324931459)
        ·
          refine ⟨88037595432531888487397189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58691730288354592324931459 88037595432531888487397189)
          ·
            refine ⟨16507049143599729091386973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88037595432531888487397189 16507049143599729091386973)
            ·
              refine ⟨6190143428849898409270115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16507049143599729091386973 6190143428849898409270115)
              ·
                refine ⟨9285215143274847613905173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190143428849898409270115 9285215143274847613905173)
                ·
                  refine ⟨435244459841008481901805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9285215143274847613905173 435244459841008481901805)
                  ·
                    refine ⟨163216672440378180713177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435244459841008481901805 163216672440378180713177)
                    ·
                      rfl

theorem cell22_476795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].length) (baseStart_476795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476795 prefixEnd_476795 := by exact prefixLift 476795
  have htrace : WordTrace (prefixWord ++ tailWord_476795) baseStart_476795 baseEnd_476795 := by
    simpa [prefixWord, tailWord_476795, baseEnd_476795] using wordTrace_append hprefix tailTrace_476795
  have hstable : (prefixWord ++ tailWord_476795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476795).length < 2 ^ (prefixWord ++ tailWord_476795).sum := by decide
  have hdescent : baseEnd_476795 < baseStart_476795 := by decide
  rcases family_descends (prefixWord ++ tailWord_476795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
