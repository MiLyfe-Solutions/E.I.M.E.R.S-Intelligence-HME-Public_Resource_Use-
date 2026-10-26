import V185TrunkScan23Chunk1208

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7162111 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_7162111 : Nat := 118140960795 + 7162111 * 2 ^ 59
def prefixEnd_7162111 : Nat := 4983230072969 + 3 ^ 40 * 7162111 * 2
def baseEnd_7162111 : Nat := 3677605443853732941474557

theorem tailTrace_7162111 : CollatzResearch.WordTrace tailWord_7162111 prefixEnd_7162111 3677605443853732941474557 := by
  unfold tailWord_7162111
  simp only [CollatzResearch.WordTrace]
  refine ⟨261223648555902513020686187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174149099037268342013790791 261223648555902513020686187)
  ·
    refine ⟨391835472833853769531029281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261223648555902513020686187 391835472833853769531029281)
    ·
      refine ⟨293876604625390327148271961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391835472833853769531029281 293876604625390327148271961)
      ·
        refine ⟨220407453469042745361203971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293876604625390327148271961 220407453469042745361203971)
        ·
          refine ⟨330611180203564118041805957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220407453469042745361203971 330611180203564118041805957)
          ·
            refine ⟨61989596288168272132838617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330611180203564118041805957 61989596288168272132838617)
            ·
              refine ⟨46492197216126204099628963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61989596288168272132838617 46492197216126204099628963)
              ·
                refine ⟨69738295824189306149443445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46492197216126204099628963 69738295824189306149443445)
                ·
                  refine ⟨6537965233517747451510323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69738295824189306149443445 6537965233517747451510323)
                  ·
                    refine ⟨9806947850276621177265485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6537965233517747451510323 9806947850276621177265485)
                    ·
                      refine ⟨3677605443853732941474557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9806947850276621177265485 3677605443853732941474557)
                      ·
                        rfl

theorem cell23_7162111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_7162111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162111 prefixEnd_7162111 := by exact prefixLift 7162111
  have htrace : WordTrace (prefixWord ++ tailWord_7162111) baseStart_7162111 baseEnd_7162111 := by
    simpa [prefixWord, tailWord_7162111, baseEnd_7162111] using wordTrace_append hprefix tailTrace_7162111
  have hstable : (prefixWord ++ tailWord_7162111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162111).length < 2 ^ (prefixWord ++ tailWord_7162111).sum := by decide
  have hdescent : baseEnd_7162111 < baseStart_7162111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162168 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_7162168 : Nat := 118140960795 + 7162168 * 2 ^ 59
def prefixEnd_7162168 : Nat := 4983230072969 + 3 ^ 40 * 7162168 * 2
def baseEnd_7162168 : Nat := 3677634712251039218461795

theorem tailTrace_7162168 : CollatzResearch.WordTrace tailWord_7162168 prefixEnd_7162168 3677634712251039218461795 := by
  unfold tailWord_7162168
  simp only [CollatzResearch.WordTrace]
  refine ⟨130612863758348005877755579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174150485011130674503674105 130612863758348005877755579)
  ·
    refine ⟨195919295637522008816633369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130612863758348005877755579 195919295637522008816633369)
    ·
      refine ⟨146939471728141506612475027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195919295637522008816633369 146939471728141506612475027)
      ·
        refine ⟨220409207592212259918712541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146939471728141506612475027 220409207592212259918712541)
        ·
          refine ⟨82653452847079597469517203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220409207592212259918712541 82653452847079597469517203)
          ·
            refine ⟨123980179270619396204275805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82653452847079597469517203 123980179270619396204275805)
            ·
              refine ⟨46492567226482273576603427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123980179270619396204275805 46492567226482273576603427)
              ·
                refine ⟨69738850839723410364905141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46492567226482273576603427 69738850839723410364905141)
                ·
                  refine ⟨6538017266224069721709857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69738850839723410364905141 6538017266224069721709857)
                  ·
                    refine ⟨4903512949668052291282393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6538017266224069721709857 4903512949668052291282393)
                    ·
                      refine ⟨3677634712251039218461795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903512949668052291282393 3677634712251039218461795)
                      ·
                        rfl

theorem cell23_7162168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_7162168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162168 prefixEnd_7162168 := by exact prefixLift 7162168
  have htrace : WordTrace (prefixWord ++ tailWord_7162168) baseStart_7162168 baseEnd_7162168 := by
    simpa [prefixWord, tailWord_7162168, baseEnd_7162168] using wordTrace_append hprefix tailTrace_7162168
  have hstable : (prefixWord ++ tailWord_7162168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162168).length < 2 ^ (prefixWord ++ tailWord_7162168).sum := by decide
  have hdescent : baseEnd_7162168 < baseStart_7162168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162188 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7162188 : Nat := 118140960795 + 7162188 * 2 ^ 59
def prefixEnd_7162188 : Nat := 4983230072969 + 3 ^ 40 * 7162188 * 2
def baseEnd_7162188 : Nat := 3677644981864129140211703

theorem tailTrace_7162188 : CollatzResearch.WordTrace tailWord_7162188 prefixEnd_7162188 3677644981864129140211703 := by
  unfold tailWord_7162188
  simp only [CollatzResearch.WordTrace]
  refine ⟨130613228488311777585619609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174150971317749036780826145 130613228488311777585619609)
  ·
    refine ⟨97959921366233833189214707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130613228488311777585619609 97959921366233833189214707)
    ·
      refine ⟨146939882049350749783822061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97959921366233833189214707 146939882049350749783822061)
      ·
        refine ⟨55102455768506531168933273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146939882049350749783822061 55102455768506531168933273)
        ·
          refine ⟨41326841826379898376699955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55102455768506531168933273 41326841826379898376699955)
          ·
            refine ⟨61990262739569847565049933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41326841826379898376699955 61990262739569847565049933)
            ·
              refine ⟨23246348527338692836893725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61990262739569847565049933 23246348527338692836893725)
              ·
                refine ⟨8717380697752009813835147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23246348527338692836893725 8717380697752009813835147)
                ·
                  refine ⟨13076071046628014720752721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717380697752009813835147 13076071046628014720752721)
                  ·
                    refine ⟨9807053284971011040564541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13076071046628014720752721 9807053284971011040564541)
                    ·
                      refine ⟨3677644981864129140211703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807053284971011040564541 3677644981864129140211703)
                      ·
                        rfl

theorem cell23_7162188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7162188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162188 prefixEnd_7162188 := by exact prefixLift 7162188
  have htrace : WordTrace (prefixWord ++ tailWord_7162188) baseStart_7162188 baseEnd_7162188 := by
    simpa [prefixWord, tailWord_7162188, baseEnd_7162188] using wordTrace_append hprefix tailTrace_7162188
  have hstable : (prefixWord ++ tailWord_7162188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162188).length < 2 ^ (prefixWord ++ tailWord_7162188).sum := by decide
  have hdescent : baseEnd_7162188 < baseStart_7162188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162261 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_7162261 : Nat := 118140960795 + 7162261 * 2 ^ 59
def prefixEnd_7162261 : Nat := 4983230072969 + 3 ^ 40 * 7162261 * 2
def baseEnd_7162261 : Nat := 3677682465951907354598867

theorem tailTrace_7162261 : CollatzResearch.WordTrace tailWord_7162261 prefixEnd_7162261 3677682465951907354598867 := by
  unfold tailWord_7162261
  simp only [CollatzResearch.WordTrace]
  refine ⟨261229119505359088638646637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174152746336906059092431091 261229119505359088638646637)
  ·
    refine ⟨97960919814509658239492489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261229119505359088638646637 97960919814509658239492489)
    ·
      refine ⟨73470689860882243679619367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97960919814509658239492489 73470689860882243679619367)
      ·
        refine ⟨110206034791323365519429051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73470689860882243679619367 110206034791323365519429051)
        ·
          refine ⟨165309052186985048279143577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110206034791323365519429051 165309052186985048279143577)
          ·
            refine ⟨123981789140238786209357683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165309052186985048279143577 123981789140238786209357683)
            ·
              refine ⟨185972683710358179314036525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123981789140238786209357683 185972683710358179314036525)
              ·
                refine ⟨69739756391384317242763697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185972683710358179314036525 69739756391384317242763697)
                ·
                  refine ⟨52304817293538237932072773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69739756391384317242763697 52304817293538237932072773)
                  ·
                    refine ⟨9807153242538419612263645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52304817293538237932072773 9807153242538419612263645)
                    ·
                      refine ⟨3677682465951907354598867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807153242538419612263645 3677682465951907354598867)
                      ·
                        rfl

theorem cell23_7162261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_7162261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162261 prefixEnd_7162261 := by exact prefixLift 7162261
  have htrace : WordTrace (prefixWord ++ tailWord_7162261) baseStart_7162261 baseEnd_7162261 := by
    simpa [prefixWord, tailWord_7162261, baseEnd_7162261] using wordTrace_append hprefix tailTrace_7162261
  have hstable : (prefixWord ++ tailWord_7162261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162261).length < 2 ^ (prefixWord ++ tailWord_7162261).sum := by decide
  have hdescent : baseEnd_7162261 < baseStart_7162261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162269 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_7162269 : Nat := 118140960795 + 7162269 * 2 ^ 59
def prefixEnd_7162269 : Nat := 4983230072969 + 3 ^ 40 * 7162269 * 2
def baseEnd_7162269 : Nat := 3677686573797143323298831

theorem tailTrace_7162269 : CollatzResearch.WordTrace tailWord_7162269 prefixEnd_7162269 3677686573797143323298831 := by
  unfold tailWord_7162269
  simp only [CollatzResearch.WordTrace]
  refine ⟨261229411289330106004937861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174152940859553404003291907 261229411289330106004937861)
  ·
    refine ⟨48980514616749394875925849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261229411289330106004937861 48980514616749394875925849)
    ·
      refine ⟨36735385962562046156944387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48980514616749394875925849 36735385962562046156944387)
      ·
        refine ⟨55103078943843069235416581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36735385962562046156944387 55103078943843069235416581)
        ·
          refine ⟨10331827301970575481640609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55103078943843069235416581 10331827301970575481640609)
          ·
            refine ⟨7748870476477931611230457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331827301970575481640609 7748870476477931611230457)
            ·
              refine ⟨5811652857358448708422843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748870476477931611230457 5811652857358448708422843)
              ·
                refine ⟨8717479286037673062634265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811652857358448708422843 8717479286037673062634265)
                ·
                  refine ⟨6538109464528254796975699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8717479286037673062634265 6538109464528254796975699)
                  ·
                    refine ⟨9807164196792382195463549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538109464528254796975699 9807164196792382195463549)
                    ·
                      refine ⟨3677686573797143323298831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807164196792382195463549 3677686573797143323298831)
                      ·
                        rfl

theorem cell23_7162269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_7162269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162269 prefixEnd_7162269 := by exact prefixLift 7162269
  have htrace : WordTrace (prefixWord ++ tailWord_7162269) baseStart_7162269 baseEnd_7162269 := by
    simpa [prefixWord, tailWord_7162269, baseEnd_7162269] using wordTrace_append hprefix tailTrace_7162269
  have hstable : (prefixWord ++ tailWord_7162269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162269).length < 2 ^ (prefixWord ++ tailWord_7162269).sum := by decide
  have hdescent : baseEnd_7162269 < baseStart_7162269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162271 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7162271 : Nat := 118140960795 + 7162271 * 2 ^ 59
def prefixEnd_7162271 : Nat := 4983230072969 + 3 ^ 40 * 7162271 * 2
def baseEnd_7162271 : Nat := 3677687600758452315473821

theorem tailTrace_7162271 : CollatzResearch.WordTrace tailWord_7162271 prefixEnd_7162271 3677687600758452315473821 := by
  unfold tailWord_7162271
  simp only [CollatzResearch.WordTrace]
  refine ⟨261229484235322860346510667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174152989490215240231007111 261229484235322860346510667)
  ·
    refine ⟨391844226352984290519766001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261229484235322860346510667 391844226352984290519766001)
    ·
      refine ⟨293883169764738217889824501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391844226352984290519766001 293883169764738217889824501)
      ·
        refine ⟨27551547165444207927171047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293883169764738217889824501 27551547165444207927171047)
        ·
          refine ⟨41327320748166311890756571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27551547165444207927171047 41327320748166311890756571)
          ·
            refine ⟨61990981122249467836134857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41327320748166311890756571 61990981122249467836134857)
            ·
              refine ⟨46493235841687100877101143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61990981122249467836134857 46493235841687100877101143)
              ·
                refine ⟨69739853762530651315651715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46493235841687100877101143 69739853762530651315651715)
                ·
                  refine ⟨104609780643795976973477573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69739853762530651315651715 104609780643795976973477573)
                  ·
                    refine ⟨19614333870711745682527045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104609780643795976973477573 19614333870711745682527045)
                    ·
                      refine ⟨3677687600758452315473821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19614333870711745682527045 3677687600758452315473821)
                      ·
                        rfl

theorem cell23_7162271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7162271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162271 prefixEnd_7162271 := by exact prefixLift 7162271
  have htrace : WordTrace (prefixWord ++ tailWord_7162271) baseStart_7162271 baseEnd_7162271 := by
    simpa [prefixWord, tailWord_7162271, baseEnd_7162271] using wordTrace_append hprefix tailTrace_7162271
  have hstable : (prefixWord ++ tailWord_7162271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162271).length < 2 ^ (prefixWord ++ tailWord_7162271).sum := by decide
  have hdescent : baseEnd_7162271 < baseStart_7162271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162291 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3]
def baseStart_7162291 : Nat := 118140960795 + 7162291 * 2 ^ 59
def prefixEnd_7162291 : Nat := 4983230072969 + 3 ^ 40 * 7162291 * 2
def baseEnd_7162291 : Nat := 3677697870371542237223729

theorem tailTrace_7162291 : CollatzResearch.WordTrace tailWord_7162291 prefixEnd_7162291 3677697870371542237223729 := by
  unfold tailWord_7162291
  simp only [CollatzResearch.WordTrace]
  refine ⟨261230213695250403762238727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174153475796833602508159151 261230213695250403762238727)
  ·
    refine ⟨391845320542875605643358091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261230213695250403762238727 391845320542875605643358091)
    ·
      refine ⟨587767980814313408465037137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391845320542875605643358091 587767980814313408465037137)
      ·
        refine ⟨440825985610735056348777853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587767980814313408465037137 440825985610735056348777853)
        ·
          refine ⟨165309744604025646130791695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440825985610735056348777853 165309744604025646130791695)
          ·
            refine ⟨247964616906038469196187543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165309744604025646130791695 247964616906038469196187543)
            ·
              refine ⟨371946925359057703794281315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247964616906038469196187543 371946925359057703794281315)
              ·
                refine ⟨557920388038586555691421973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371946925359057703794281315 557920388038586555691421973)
                ·
                  refine ⟨26152518189308744798035405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557920388038586555691421973 26152518189308744798035405)
                  ·
                    refine ⟨9807194320990779299263277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26152518189308744798035405 9807194320990779299263277)
                    ·
                      refine ⟨3677697870371542237223729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807194320990779299263277 3677697870371542237223729)
                      ·
                        rfl

theorem cell23_7162291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_7162291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162291 prefixEnd_7162291 := by exact prefixLift 7162291
  have htrace : WordTrace (prefixWord ++ tailWord_7162291) baseStart_7162291 baseEnd_7162291 := by
    simpa [prefixWord, tailWord_7162291, baseEnd_7162291] using wordTrace_append hprefix tailTrace_7162291
  have hstable : (prefixWord ++ tailWord_7162291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162291).length < 2 ^ (prefixWord ++ tailWord_7162291).sum := by decide
  have hdescent : baseEnd_7162291 < baseStart_7162291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162348 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_7162348 : Nat := 118140960795 + 7162348 * 2 ^ 59
def prefixEnd_7162348 : Nat := 4983230072969 + 3 ^ 40 * 7162348 * 2
def baseEnd_7162348 : Nat := 3677727138768848514210967

theorem tailTrace_7162348 : CollatzResearch.WordTrace tailWord_7162348 prefixEnd_7162348 3677727138768848514210967 := by
  unfold tailWord_7162348
  simp only [CollatzResearch.WordTrace]
  refine ⟨130616146328021951248531849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174154861770695934998042465 130616146328021951248531849)
  ·
    refine ⟨97962109746016463436398887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130616146328021951248531849 97962109746016463436398887)
    ·
      refine ⟨146943164619024695154598331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97962109746016463436398887 146943164619024695154598331)
      ·
        refine ⟨220414746928537042731897497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146943164619024695154598331 220414746928537042731897497)
        ·
          refine ⟨165311060196402782048923123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220414746928537042731897497 165311060196402782048923123)
          ·
            refine ⟨247966590294604173073384685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165311060196402782048923123 247966590294604173073384685)
            ·
              refine ⟨92987471360476564902519257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247966590294604173073384685 92987471360476564902519257)
              ·
                refine ⟨69740603520357423676889443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92987471360476564902519257 69740603520357423676889443)
                ·
                  refine ⟨104610905280536135515334165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69740603520357423676889443 104610905280536135515334165)
                  ·
                    refine ⟨4903636185025131352281289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104610905280536135515334165 4903636185025131352281289)
                    ·
                      refine ⟨3677727138768848514210967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903636185025131352281289 3677727138768848514210967)
                      ·
                        rfl

theorem cell23_7162348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_7162348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162348 prefixEnd_7162348 := by exact prefixLift 7162348
  have htrace : WordTrace (prefixWord ++ tailWord_7162348) baseStart_7162348 baseEnd_7162348 := by
    simpa [prefixWord, tailWord_7162348, baseEnd_7162348] using wordTrace_append hprefix tailTrace_7162348
  have hstable : (prefixWord ++ tailWord_7162348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162348).length < 2 ^ (prefixWord ++ tailWord_7162348).sum := by decide
  have hdescent : baseEnd_7162348 < baseStart_7162348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162361 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7162361 : Nat := 118140960795 + 7162361 * 2 ^ 59
def prefixEnd_7162361 : Nat := 4983230072969 + 3 ^ 40 * 7162361 * 2
def baseEnd_7162361 : Nat := 3677733814017356963348407

theorem tailTrace_7162361 : CollatzResearch.WordTrace tailWord_7162361 prefixEnd_7162361 3677733814017356963348407 := by
  unfold tailWord_7162361
  simp only [CollatzResearch.WordTrace]
  refine ⟨261232766804996805717286937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174155177869997870478191291 261232766804996805717286937)
  ·
    refine ⟨195924575103747604287965203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261232766804996805717286937 195924575103747604287965203)
    ·
      refine ⟨293886862655621406431947805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195924575103747604287965203 293886862655621406431947805)
      ·
        refine ⟨110207573495858027411980427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293886862655621406431947805 110207573495858027411980427)
        ·
          refine ⟨165311360243787041117970641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110207573495858027411980427 165311360243787041117970641)
          ·
            refine ⟨123983520182840280838477981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165311360243787041117970641 123983520182840280838477981)
            ·
              refine ⟨46493820068565105314429243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123983520182840280838477981 46493820068565105314429243)
              ·
                refine ⟨69740730102847657971643865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46493820068565105314429243 69740730102847657971643865)
                ·
                  refine ⟨52305547577135743478732899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69740730102847657971643865 52305547577135743478732899)
                  ·
                    refine ⟨78458321365703615218099349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52305547577135743478732899 78458321365703615218099349)
                    ·
                      refine ⟨3677733814017356963348407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78458321365703615218099349 3677733814017356963348407)
                      ·
                        rfl

theorem cell23_7162361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7162361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162361 prefixEnd_7162361 := by exact prefixLift 7162361
  have htrace : WordTrace (prefixWord ++ tailWord_7162361) baseStart_7162361 baseEnd_7162361 := by
    simpa [prefixWord, tailWord_7162361, baseEnd_7162361] using wordTrace_append hprefix tailTrace_7162361
  have hstable : (prefixWord ++ tailWord_7162361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162361).length < 2 ^ (prefixWord ++ tailWord_7162361).sum := by decide
  have hdescent : baseEnd_7162361 < baseStart_7162361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162371 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 8]
def baseStart_7162371 : Nat := 118140960795 + 7162371 * 2 ^ 59
def prefixEnd_7162371 : Nat := 4983230072969 + 3 ^ 40 * 7162371 * 2
def baseEnd_7162371 : Nat := 408637660980433547135929

theorem tailTrace_7162371 : CollatzResearch.WordTrace tailWord_7162371 prefixEnd_7162371 408637660980433547135929 := by
  unfold tailWord_7162371
  simp only [CollatzResearch.WordTrace]
  refine ⟨261233131534960577425150967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174155421023307051616767311 261233131534960577425150967)
  ·
    refine ⟨391849697302440866137726451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261233131534960577425150967 391849697302440866137726451)
    ·
      refine ⟨587774545953661299206589677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391849697302440866137726451 587774545953661299206589677)
      ·
        refine ⟨220415454732622987202471129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587774545953661299206589677 220415454732622987202471129)
        ·
          refine ⟨165311591049467240401853347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220415454732622987202471129 165311591049467240401853347)
          ·
            refine ⟨247967386574200860602780021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165311591049467240401853347 247967386574200860602780021)
            ·
              refine ⟨23246942491331330681510627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247967386574200860602780021 23246942491331330681510627)
              ·
                refine ⟨34870413736996996022265941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23246942491331330681510627 34870413736996996022265941)
                ·
                  refine ⟨408637660980433547135929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34870413736996996022265941 408637660980433547135929)
                  ·
                    rfl

theorem cell23_7162371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 8].length) (baseStart_7162371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162371 prefixEnd_7162371 := by exact prefixLift 7162371
  have htrace : WordTrace (prefixWord ++ tailWord_7162371) baseStart_7162371 baseEnd_7162371 := by
    simpa [prefixWord, tailWord_7162371, baseEnd_7162371] using wordTrace_append hprefix tailTrace_7162371
  have hstable : (prefixWord ++ tailWord_7162371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162371).length < 2 ^ (prefixWord ++ tailWord_7162371).sum := by decide
  have hdescent : baseEnd_7162371 < baseStart_7162371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162432 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 1, 1, 3]
def baseStart_7162432 : Nat := 118140960795 + 7162432 * 2 ^ 59
def prefixEnd_7162432 : Nat := 4983230072969 + 3 ^ 40 * 7162432 * 2
def baseEnd_7162432 : Nat := 3677770271143826185560581

theorem tailTrace_7162432 : CollatzResearch.WordTrace tailWord_7162432 prefixEnd_7162432 3677770271143826185560581 := by
  unfold tailWord_7162432
  simp only [CollatzResearch.WordTrace]
  refine ⟨130617678193869792421560775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174156904258493056562081033 130617678193869792421560775)
  ·
    refine ⟨195926517290804688632341163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130617678193869792421560775 195926517290804688632341163)
    ·
      refine ⟨293889775936207032948511745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195926517290804688632341163 293889775936207032948511745)
      ·
        refine ⟨220417331952155274711383809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293889775936207032948511745 220417331952155274711383809)
        ·
          refine ⟨165312998964116456033537857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220417331952155274711383809 165312998964116456033537857)
          ·
            refine ⟨123984749223087342025153393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165312998964116456033537857 123984749223087342025153393)
            ·
              refine ⟨92988561917315506518865045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123984749223087342025153393 92988561917315506518865045)
              ·
                refine ⟨4358838839874164368071799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92988561917315506518865045 4358838839874164368071799)
                ·
                  refine ⟨6538258259811246552107699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4358838839874164368071799 6538258259811246552107699)
                  ·
                    refine ⟨9807387389716869828161549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538258259811246552107699 9807387389716869828161549)
                    ·
                      refine ⟨3677770271143826185560581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807387389716869828161549 3677770271143826185560581)
                      ·
                        rfl

theorem cell23_7162432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_7162432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162432 prefixEnd_7162432 := by exact prefixLift 7162432
  have htrace : WordTrace (prefixWord ++ tailWord_7162432) baseStart_7162432 baseEnd_7162432 := by
    simpa [prefixWord, tailWord_7162432, baseEnd_7162432] using wordTrace_append hprefix tailTrace_7162432
  have hstable : (prefixWord ++ tailWord_7162432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162432).length < 2 ^ (prefixWord ++ tailWord_7162432).sum := by decide
  have hdescent : baseEnd_7162432 < baseStart_7162432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162448 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_7162448 : Nat := 118140960795 + 7162448 * 2 ^ 59
def prefixEnd_7162448 : Nat := 4983230072969 + 3 ^ 40 * 7162448 * 2
def baseEnd_7162448 : Nat := 1225926162278099374320169

theorem tailTrace_7162448 : CollatzResearch.WordTrace tailWord_7162448 prefixEnd_7162448 1225926162278099374320169 := by
  unfold tailWord_7162448
  simp only [CollatzResearch.WordTrace]
  refine ⟨130617969977840809787851999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174157293303787746383802665 130617969977840809787851999)
  ·
    refine ⟨195926954966761214681777999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130617969977840809787851999 195926954966761214681777999)
    ·
      refine ⟨293890432450141822022666999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195926954966761214681777999 293890432450141822022666999)
      ·
        refine ⟨440835648675212733034000499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293890432450141822022666999 440835648675212733034000499)
        ·
          refine ⟨661253473012819099551000749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440835648675212733034000499 661253473012819099551000749)
          ·
            refine ⟨247970052379807162331625281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661253473012819099551000749 247970052379807162331625281)
            ·
              refine ⟨185977539284855371748718961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247970052379807162331625281 185977539284855371748718961)
              ·
                refine ⟨139483154463641528811539221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185977539284855371748718961 139483154463641528811539221)
                ·
                  refine ⟨6538272865483196663040901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139483154463641528811539221 6538272865483196663040901)
                  ·
                    refine ⟨1225926162278099374320169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6538272865483196663040901 1225926162278099374320169)
                    ·
                      rfl

theorem cell23_7162448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_7162448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162448 prefixEnd_7162448 := by exact prefixLift 7162448
  have htrace : WordTrace (prefixWord ++ tailWord_7162448) baseStart_7162448 baseEnd_7162448 := by
    simpa [prefixWord, tailWord_7162448, baseEnd_7162448] using wordTrace_append hprefix tailTrace_7162448
  have hstable : (prefixWord ++ tailWord_7162448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162448).length < 2 ^ (prefixWord ++ tailWord_7162448).sum := by decide
  have hdescent : baseEnd_7162448 < baseStart_7162448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162452 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_7162452 : Nat := 118140960795 + 7162452 * 2 ^ 59
def prefixEnd_7162452 : Nat := 4983230072969 + 3 ^ 40 * 7162452 * 2
def baseEnd_7162452 : Nat := 1225926846918972035770163

theorem tailTrace_7162452 : CollatzResearch.WordTrace tailWord_7162452 prefixEnd_7162452 1225926846918972035770163 := by
  unfold tailWord_7162452
  simp only [CollatzResearch.WordTrace]
  refine ⟨130618042923833564129424805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174157390565111418839233073 130618042923833564129424805)
  ·
    refine ⟨24490883048218793274267151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130618042923833564129424805 24490883048218793274267151)
    ·
      refine ⟨36736324572328189911400727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24490883048218793274267151 36736324572328189911400727)
      ·
        refine ⟨55104486858492284867101091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36736324572328189911400727 55104486858492284867101091)
        ·
          refine ⟨82656730287738427300651637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55104486858492284867101091 82656730287738427300651637)
          ·
            refine ⟨7749068464475477559436091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82656730287738427300651637 7749068464475477559436091)
            ·
              refine ⟨11623602696713216339154137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749068464475477559436091 11623602696713216339154137)
              ·
                refine ⟨8717702022534912254365603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11623602696713216339154137 8717702022534912254365603)
                ·
                  refine ⟨13076553033802368381548405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717702022534912254365603 13076553033802368381548405)
                  ·
                    refine ⟨1225926846918972035770163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13076553033802368381548405 1225926846918972035770163)
                    ·
                      rfl

theorem cell23_7162452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_7162452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162452 prefixEnd_7162452 := by exact prefixLift 7162452
  have htrace : WordTrace (prefixWord ++ tailWord_7162452) baseStart_7162452 baseEnd_7162452 := by
    simpa [prefixWord, tailWord_7162452, baseEnd_7162452] using wordTrace_append hprefix tailTrace_7162452
  have hstable : (prefixWord ++ tailWord_7162452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162452).length < 2 ^ (prefixWord ++ tailWord_7162452).sum := by decide
  have hdescent : baseEnd_7162452 < baseStart_7162452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162478 : List Nat := [4, 1, 2, 2, 2, 12]
def baseStart_7162478 : Nat := 118140960795 + 7162478 * 2 ^ 59
def prefixEnd_7162478 : Nat := 4983230072969 + 3 ^ 40 * 7162478 * 2
def baseEnd_7162478 : Nat := 15134954284995609076483

theorem tailTrace_7162478 : CollatzResearch.WordTrace tailWord_7162478 prefixEnd_7162478 15134954284995609076483 := by
  unfold tailWord_7162478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654629268196616837412011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174158022763715289799530725 32654629268196616837412011)
  ·
    refine ⟨48981943902294925256118017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32654629268196616837412011 48981943902294925256118017)
    ·
      refine ⟨36736457926721193942088513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48981943902294925256118017 36736457926721193942088513)
      ·
        refine ⟨27552343445040895456566385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36736457926721193942088513 27552343445040895456566385)
        ·
          refine ⟨20664257583780671592424789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27552343445040895456566385 20664257583780671592424789)
          ·
            refine ⟨15134954284995609076483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20664257583780671592424789 15134954284995609076483)
            ·
              rfl

theorem cell23_7162478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 12].length) (baseStart_7162478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162478 prefixEnd_7162478 := by exact prefixLift 7162478
  have htrace : WordTrace (prefixWord ++ tailWord_7162478) baseStart_7162478 baseEnd_7162478 := by
    simpa [prefixWord, tailWord_7162478, baseEnd_7162478] using wordTrace_append hprefix tailTrace_7162478
  have hstable : (prefixWord ++ tailWord_7162478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162478).length < 2 ^ (prefixWord ++ tailWord_7162478).sum := by decide
  have hdescent : baseEnd_7162478 < baseStart_7162478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162505 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_7162505 : Nat := 118140960795 + 7162505 * 2 ^ 59
def prefixEnd_7162505 : Nat := 4983230072969 + 3 ^ 40 * 7162505 * 2
def baseEnd_7162505 : Nat := 3677807755231604399947745

theorem tailTrace_7162505 : CollatzResearch.WordTrace tailWord_7162505 prefixEnd_7162505 3677807755231604399947745 := by
  unfold tailWord_7162505
  simp only [CollatzResearch.WordTrace]
  refine ⟨261238018916475118310528969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174158679277650078873685979 261238018916475118310528969)
  ·
    refine ⟨195928514187356338732896727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261238018916475118310528969 195928514187356338732896727)
    ·
      refine ⟨293892771281034508099345091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195928514187356338732896727 293892771281034508099345091)
      ·
        refine ⟨440839156921551762149017637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293892771281034508099345091 440839156921551762149017637)
        ·
          refine ⟨82657341922790955402940807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440839156921551762149017637 82657341922790955402940807)
          ·
            refine ⟨123986012884186433104411211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82657341922790955402940807 123986012884186433104411211)
            ·
              refine ⟨185979019326279649656616817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123986012884186433104411211 185979019326279649656616817)
              ·
                refine ⟨139484264494709737242462613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185979019326279649656616817 139484264494709737242462613)
                ·
                  refine ⟨6538324898189518933240435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139484264494709737242462613 6538324898189518933240435)
                  ·
                    refine ⟨9807487347284278399860653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538324898189518933240435 9807487347284278399860653)
                    ·
                      refine ⟨3677807755231604399947745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807487347284278399860653 3677807755231604399947745)
                      ·
                        rfl

theorem cell23_7162505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_7162505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162505 prefixEnd_7162505 := by exact prefixLift 7162505
  have htrace : WordTrace (prefixWord ++ tailWord_7162505) baseStart_7162505 baseEnd_7162505 := by
    simpa [prefixWord, tailWord_7162505, baseEnd_7162505] using wordTrace_append hprefix tailTrace_7162505
  have hstable : (prefixWord ++ tailWord_7162505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162505).length < 2 ^ (prefixWord ++ tailWord_7162505).sum := by decide
  have hdescent : baseEnd_7162505 < baseStart_7162505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162632 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_7162632 : Nat := 118140960795 + 7162632 * 2 ^ 59
def prefixEnd_7162632 : Nat := 4983230072969 + 3 ^ 40 * 7162632 * 2
def baseEnd_7162632 : Nat := 1225957655758241801019887

theorem tailTrace_7162632 : CollatzResearch.WordTrace tailWord_7162632 prefixEnd_7162632 1225957655758241801019887 := by
  unfold tailWord_7162632
  simp only [CollatzResearch.WordTrace]
  refine ⟨130621325493507509500201075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174161767324676679333601433 130621325493507509500201075)
  ·
    refine ⟨195931988240261264250301613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130621325493507509500201075 195931988240261264250301613)
    ·
      refine ⟨73474495590097974093863105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195931988240261264250301613 73474495590097974093863105)
      ·
        refine ⟨55105871692573480570397329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73474495590097974093863105 55105871692573480570397329)
        ·
          refine ⟨41329403769430110427797997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55105871692573480570397329 41329403769430110427797997)
          ·
            refine ⟨15498526413536291410424249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41329403769430110427797997 15498526413536291410424249)
            ·
              refine ⟨11623894810152218557818187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15498526413536291410424249 11623894810152218557818187)
              ·
                refine ⟨17435842215228327836727281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623894810152218557818187 17435842215228327836727281)
                ·
                  refine ⟨13076881661421245877545461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17435842215228327836727281 13076881661421245877545461)
                  ·
                    refine ⟨1225957655758241801019887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13076881661421245877545461 1225957655758241801019887)
                    ·
                      rfl

theorem cell23_7162632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_7162632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162632 prefixEnd_7162632 := by exact prefixLift 7162632
  have htrace : WordTrace (prefixWord ++ tailWord_7162632) baseStart_7162632 baseEnd_7162632 := by
    simpa [prefixWord, tailWord_7162632, baseEnd_7162632] using wordTrace_append hprefix tailTrace_7162632
  have hstable : (prefixWord ++ tailWord_7162632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162632).length < 2 ^ (prefixWord ++ tailWord_7162632).sum := by decide
  have hdescent : baseEnd_7162632 < baseStart_7162632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162652 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7162652 : Nat := 118140960795 + 7162652 * 2 ^ 59
def prefixEnd_7162652 : Nat := 4983230072969 + 3 ^ 40 * 7162652 * 2
def baseEnd_7162652 : Nat := 3677883236887815324809569

theorem tailTrace_7162652 : CollatzResearch.WordTrace tailWord_7162652 prefixEnd_7162652 3677883236887815324809569 := by
  unfold tailWord_7162652
  simp only [CollatzResearch.WordTrace]
  refine ⟨130621690223471281208065105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174162253631295041610753473 130621690223471281208065105)
  ·
    refine ⟨97966267667603460906048829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130621690223471281208065105 97966267667603460906048829)
    ·
      refine ⟨36737350375351297839768311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97966267667603460906048829 36737350375351297839768311)
      ·
        refine ⟨55106025563026946759652467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36737350375351297839768311 55106025563026946759652467)
        ·
          refine ⟨82659038344540420139478701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55106025563026946759652467 82659038344540420139478701)
          ·
            refine ⟨30997139379202657552304513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82659038344540420139478701 30997139379202657552304513)
            ·
              refine ⟨23247854534401993164228385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997139379202657552304513 23247854534401993164228385)
              ·
                refine ⟨17435890900801494873171289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23247854534401993164228385 17435890900801494873171289)
                ·
                  refine ⟨13076918175601121154878467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17435890900801494873171289 13076918175601121154878467)
                  ·
                    refine ⟨19615377263401681732317701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13076918175601121154878467 19615377263401681732317701)
                    ·
                      refine ⟨3677883236887815324809569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19615377263401681732317701 3677883236887815324809569)
                      ·
                        rfl

theorem cell23_7162652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7162652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162652 prefixEnd_7162652 := by exact prefixLift 7162652
  have htrace : WordTrace (prefixWord ++ tailWord_7162652) baseStart_7162652 baseEnd_7162652 := by
    simpa [prefixWord, tailWord_7162652, baseEnd_7162652] using wordTrace_append hprefix tailTrace_7162652
  have hstable : (prefixWord ++ tailWord_7162652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162652).length < 2 ^ (prefixWord ++ tailWord_7162652).sum := by decide
  have hdescent : baseEnd_7162652 < baseStart_7162652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162653 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 5]
def baseStart_7162653 : Nat := 118140960795 + 7162653 * 2 ^ 59
def prefixEnd_7162653 : Nat := 4983230072969 + 3 ^ 40 * 7162653 * 2
def baseEnd_7162653 : Nat := 408653750040941091210785

theorem tailTrace_7162653 : CollatzResearch.WordTrace tailWord_7162653 prefixEnd_7162653 408653750040941091210785 := by
  unfold tailWord_7162653
  simp only [CollatzResearch.WordTrace]
  refine ⟨261243416919938939586916613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174162277946625959724611075 261243416919938939586916613)
  ·
    refine ⟨48983140672488551172546865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261243416919938939586916613 48983140672488551172546865)
    ·
      refine ⟨36737355504366413379410149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48983140672488551172546865 36737355504366413379410149)
      ·
        refine ⟨6888254157068702508639403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36737355504366413379410149 6888254157068702508639403)
        ·
          refine ⟨10332381235603053762959105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888254157068702508639403 10332381235603053762959105)
          ·
            refine ⟨7749285926702290322219329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10332381235603053762959105 7749285926702290322219329)
            ·
              refine ⟨5811964445026717741664497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749285926702290322219329 5811964445026717741664497)
              ·
                refine ⟨4358973333770038306248373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811964445026717741664497 4358973333770038306248373)
                ·
                  refine ⟨408653750040941091210785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4358973333770038306248373 408653750040941091210785)
                  ·
                    rfl

theorem cell23_7162653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_7162653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162653 prefixEnd_7162653 := by exact prefixLift 7162653
  have htrace : WordTrace (prefixWord ++ tailWord_7162653) baseStart_7162653 baseEnd_7162653 := by
    simpa [prefixWord, tailWord_7162653, baseEnd_7162653] using wordTrace_append hprefix tailTrace_7162653
  have hstable : (prefixWord ++ tailWord_7162653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162653).length < 2 ^ (prefixWord ++ tailWord_7162653).sum := by decide
  have hdescent : baseEnd_7162653 < baseStart_7162653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162686 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7162686 : Nat := 118140960795 + 7162686 * 2 ^ 59
def prefixEnd_7162686 : Nat := 4983230072969 + 3 ^ 40 * 7162686 * 2
def baseEnd_7162686 : Nat := 3677900695230068191784413

theorem tailTrace_7162686 : CollatzResearch.WordTrace tailWord_7162686 prefixEnd_7162686 3677900695230068191784413 := by
  unfold tailWord_7162686
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655577566102423277858489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174163080352546257481911941 32655577566102423277858489)
  ·
    refine ⟨24491683174576817458393867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32655577566102423277858489 24491683174576817458393867)
    ·
      refine ⟨36737524761865226187590801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24491683174576817458393867 36737524761865226187590801)
      ·
        refine ⟨27553143571398919640693101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36737524761865226187590801 27553143571398919640693101)
        ·
          refine ⟨10332428839274594865259913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27553143571398919640693101 10332428839274594865259913)
          ·
            refine ⟨7749321629455946148944935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10332428839274594865259913 7749321629455946148944935)
            ·
              refine ⟨11623982444183919223417403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749321629455946148944935 11623982444183919223417403)
              ·
                refine ⟨17435973666275878835126105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623982444183919223417403 17435973666275878835126105)
                ·
                  refine ⟨13076980249706909126344579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17435973666275878835126105 13076980249706909126344579)
                  ·
                    refine ⟨19615470374560363689516869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13076980249706909126344579 19615470374560363689516869)
                    ·
                      refine ⟨3677900695230068191784413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19615470374560363689516869 3677900695230068191784413)
                      ·
                        rfl

theorem cell23_7162686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7162686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162686 prefixEnd_7162686 := by exact prefixLift 7162686
  have htrace : WordTrace (prefixWord ++ tailWord_7162686) baseStart_7162686 baseEnd_7162686 := by
    simpa [prefixWord, tailWord_7162686, baseEnd_7162686] using wordTrace_append hprefix tailTrace_7162686
  have hstable : (prefixWord ++ tailWord_7162686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162686).length < 2 ^ (prefixWord ++ tailWord_7162686).sum := by decide
  have hdescent : baseEnd_7162686 < baseStart_7162686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162719 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_7162719 : Nat := 118140960795 + 7162719 * 2 ^ 59
def prefixEnd_7162719 : Nat := 4983230072969 + 3 ^ 40 * 7162719 * 2
def baseEnd_7162719 : Nat := 3677917640091666562671761

theorem tailTrace_7162719 : CollatzResearch.WordTrace tailWord_7162719 prefixEnd_7162719 3677917640091666562671761 := by
  unfold tailWord_7162719
  simp only [CollatzResearch.WordTrace]
  refine ⟨261245824137699832858819211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174163882758466555239212807 261245824137699832858819211)
  ·
    refine ⟨391868736206549749288228817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261245824137699832858819211 391868736206549749288228817)
    ·
      refine ⟨293901552154912311966171613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391868736206549749288228817 293901552154912311966171613)
      ·
        refine ⟨110213082058092116987314355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293901552154912311966171613 110213082058092116987314355)
        ·
          refine ⟨165319623087138175480971533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110213082058092116987314355 165319623087138175480971533)
          ·
            refine ⟨61994858657676815805364325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165319623087138175480971533 61994858657676815805364325)
            ·
              refine ⟨11624035998314402963505811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61994858657676815805364325 11624035998314402963505811)
              ·
                refine ⟨17436053997471604445258717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11624035998314402963505811 17436053997471604445258717)
                ·
                  refine ⟨6538520249051851666972019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17436053997471604445258717 6538520249051851666972019)
                  ·
                    refine ⟨9807780373577777500458029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538520249051851666972019 9807780373577777500458029)
                    ·
                      refine ⟨3677917640091666562671761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807780373577777500458029 3677917640091666562671761)
                      ·
                        rfl

theorem cell23_7162719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_7162719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162719 prefixEnd_7162719 := by exact prefixLift 7162719
  have htrace : WordTrace (prefixWord ++ tailWord_7162719) baseStart_7162719 baseEnd_7162719 := by
    simpa [prefixWord, tailWord_7162719, baseEnd_7162719] using wordTrace_append hprefix tailTrace_7162719
  have hstable : (prefixWord ++ tailWord_7162719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162719).length < 2 ^ (prefixWord ++ tailWord_7162719).sum := by decide
  have hdescent : baseEnd_7162719 < baseStart_7162719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162759 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_7162759 : Nat := 118140960795 + 7162759 * 2 ^ 59
def prefixEnd_7162759 : Nat := 4983230072969 + 3 ^ 40 * 7162759 * 2
def baseEnd_7162759 : Nat := 3677938179317846406171577

theorem tailTrace_7162759 : CollatzResearch.WordTrace tailWord_7162759 prefixEnd_7162759 3677938179317846406171577 := by
  unfold tailWord_7162759
  simp only [CollatzResearch.WordTrace]
  refine ⟨261247283057554919690275331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174164855371703279793516887 261247283057554919690275331)
  ·
    refine ⟨391870924586332379535412997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261247283057554919690275331 391870924586332379535412997)
    ·
      refine ⟨73475798359937321162889937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391870924586332379535412997 73475798359937321162889937)
      ·
        refine ⟨55106848769952990872167453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73475798359937321162889937 55106848769952990872167453)
        ·
          refine ⟨20665068288732371577062795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55106848769952990872167453 20665068288732371577062795)
          ·
            refine ⟨30997602433098557365594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665068288732371577062795 30997602433098557365594193)
            ·
              refine ⟨23248201824823918024195645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997602433098557365594193 23248201824823918024195645)
              ·
                refine ⟨8718075684308969259073367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23248201824823918024195645 8718075684308969259073367)
                ·
                  refine ⟨13077113526463453888610051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718075684308969259073367 13077113526463453888610051)
                  ·
                    refine ⟨19615670289695180832915077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13077113526463453888610051 19615670289695180832915077)
                    ·
                      refine ⟨3677938179317846406171577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19615670289695180832915077 3677938179317846406171577)
                      ·
                        rfl

theorem cell23_7162759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_7162759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162759 prefixEnd_7162759 := by exact prefixLift 7162759
  have htrace : WordTrace (prefixWord ++ tailWord_7162759) baseStart_7162759 baseEnd_7162759 := by
    simpa [prefixWord, tailWord_7162759, baseEnd_7162759] using wordTrace_append hprefix tailTrace_7162759
  have hstable : (prefixWord ++ tailWord_7162759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162759).length < 2 ^ (prefixWord ++ tailWord_7162759).sum := by decide
  have hdescent : baseEnd_7162759 < baseStart_7162759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162770 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7162770 : Nat := 118140960795 + 7162770 * 2 ^ 59
def prefixEnd_7162770 : Nat := 4983230072969 + 3 ^ 40 * 7162770 * 2
def baseEnd_7162770 : Nat := 3677943827605045863134027

theorem tailTrace_7162770 : CollatzResearch.WordTrace tailWord_7162770 prefixEnd_7162770 3677943827605045863134027 := by
  unfold tailWord_7162770
  simp only [CollatzResearch.WordTrace]
  refine ⟨65311921065128767142231441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174165122840343379045950509 65311921065128767142231441)
  ·
    refine ⟨48983940798846575356673581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65311921065128767142231441 48983940798846575356673581)
    ·
      refine ⟨18368977799567465758752593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48983940798846575356673581 18368977799567465758752593)
      ·
        refine ⟨13776733349675599319064445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18368977799567465758752593 13776733349675599319064445)
        ·
          refine ⟨5166275006128349744649167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13776733349675599319064445 5166275006128349744649167)
          ·
            refine ⟨7749412509192524616973751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166275006128349744649167 7749412509192524616973751)
            ·
              refine ⟨11624118763788786925460627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749412509192524616973751 11624118763788786925460627)
              ·
                refine ⟨17436178145683180388190941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11624118763788786925460627 17436178145683180388190941)
                ·
                  refine ⟨6538566804631192645571603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17436178145683180388190941 6538566804631192645571603)
                  ·
                    refine ⟨9807850206946788968357405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538566804631192645571603 9807850206946788968357405)
                    ·
                      refine ⟨3677943827605045863134027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807850206946788968357405 3677943827605045863134027)
                      ·
                        rfl

theorem cell23_7162770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7162770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162770 prefixEnd_7162770 := by exact prefixLift 7162770
  have htrace : WordTrace (prefixWord ++ tailWord_7162770) baseStart_7162770 baseEnd_7162770 := by
    simpa [prefixWord, tailWord_7162770, baseEnd_7162770] using wordTrace_append hprefix tailTrace_7162770
  have hstable : (prefixWord ++ tailWord_7162770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162770).length < 2 ^ (prefixWord ++ tailWord_7162770).sum := by decide
  have hdescent : baseEnd_7162770 < baseStart_7162770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162772 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7162772 : Nat := 118140960795 + 7162772 * 2 ^ 59
def prefixEnd_7162772 : Nat := 4983230072969 + 3 ^ 40 * 7162772 * 2
def baseEnd_7162772 : Nat := 3677944854566354855309017

theorem tailTrace_7162772 : CollatzResearch.WordTrace tailWord_7162772 prefixEnd_7162772 3677944854566354855309017 := by
  unfold tailWord_7162772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130623878603253911455249285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174165171471005215273665713 130623878603253911455249285)
  ·
    refine ⟨24491977238110108397859241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130623878603253911455249285 24491977238110108397859241)
    ·
      refine ⟨18368982928582581298394431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24491977238110108397859241 18368982928582581298394431)
      ·
        refine ⟨27553474392873871947591647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18368982928582581298394431 27553474392873871947591647)
        ·
          refine ⟨41330211589310807921387471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27553474392873871947591647 41330211589310807921387471)
          ·
            refine ⟨61995317383966211882081207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41330211589310807921387471 61995317383966211882081207)
            ·
              refine ⟨92992976075949317823121811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61995317383966211882081207 92992976075949317823121811)
              ·
                refine ⟨139489464113923976734682717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92992976075949317823121811 139489464113923976734682717)
                ·
                  refine ⟨52308549042721491275506019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139489464113923976734682717 52308549042721491275506019)
                  ·
                    refine ⟨78462823564082236913259029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52308549042721491275506019 78462823564082236913259029)
                    ·
                      refine ⟨3677944854566354855309017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78462823564082236913259029 3677944854566354855309017)
                      ·
                        rfl

theorem cell23_7162772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7162772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162772 prefixEnd_7162772 := by exact prefixLift 7162772
  have htrace : WordTrace (prefixWord ++ tailWord_7162772) baseStart_7162772 baseEnd_7162772 := by
    simpa [prefixWord, tailWord_7162772, baseEnd_7162772] using wordTrace_append hprefix tailTrace_7162772
  have hstable : (prefixWord ++ tailWord_7162772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162772).length < 2 ^ (prefixWord ++ tailWord_7162772).sum := by decide
  have hdescent : baseEnd_7162772 < baseStart_7162772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162786 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7162786 : Nat := 118140960795 + 7162786 * 2 ^ 59
def prefixEnd_7162786 : Nat := 4983230072969 + 3 ^ 40 * 7162786 * 2
def baseEnd_7162786 : Nat := 1225984014431839266844651

theorem tailTrace_7162786 : CollatzResearch.WordTrace tailWord_7162786 prefixEnd_7162786 1225984014431839266844651 := by
  unfold tailWord_7162786
  simp only [CollatzResearch.WordTrace]
  refine ⟨65312066957114275825377053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174165511885638068867672141 65312066957114275825377053)
  ·
    refine ⟨24492025108917853434516395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65312066957114275825377053 24492025108917853434516395)
    ·
      refine ⟨36738037663376780151774593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492025108917853434516395 36738037663376780151774593)
      ·
        refine ⟨27553528247532585113830945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36738037663376780151774593 27553528247532585113830945)
        ·
          refine ⟨20665146185649438835373209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27553528247532585113830945 20665146185649438835373209)
          ·
            refine ⟨15498859639237079126529907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20665146185649438835373209 15498859639237079126529907)
            ·
              refine ⟨23248289458855618689794861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15498859639237079126529907 23248289458855618689794861)
              ·
                refine ⟨8718108547070857008673073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23248289458855618689794861 8718108547070857008673073)
                ·
                  refine ⟨6538581410303142756504805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718108547070857008673073 6538581410303142756504805)
                  ·
                    refine ⟨1225984014431839266844651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6538581410303142756504805 1225984014431839266844651)
                    ·
                      rfl

theorem cell23_7162786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7162786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162786 prefixEnd_7162786 := by exact prefixLift 7162786
  have htrace : WordTrace (prefixWord ++ tailWord_7162786) baseStart_7162786 baseEnd_7162786 := by
    simpa [prefixWord, tailWord_7162786, baseEnd_7162786] using wordTrace_append hprefix tailTrace_7162786
  have hstable : (prefixWord ++ tailWord_7162786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162786).length < 2 ^ (prefixWord ++ tailWord_7162786).sum := by decide
  have hdescent : baseEnd_7162786 < baseStart_7162786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162795 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 7]
def baseStart_7162795 : Nat := 118140960795 + 7162795 * 2 ^ 59
def prefixEnd_7162795 : Nat := 4983230072969 + 3 ^ 40 * 7162795 * 2
def baseEnd_7162795 : Nat := 1225985554873802755107137

theorem tailTrace_7162795 : CollatzResearch.WordTrace tailWord_7162795 prefixEnd_7162795 1225985554873802755107137 := by
  unfold tailWord_7162795
  simp only [CollatzResearch.WordTrace]
  refine ⟨261248596085424497838585839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174165730723616331892390559 261248596085424497838585839)
  ·
    refine ⟨391872894128136746757878759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261248596085424497838585839 391872894128136746757878759)
    ·
      refine ⟨587809341192205120136818139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391872894128136746757878759 587809341192205120136818139)
      ·
        refine ⟨881714011788307680205227209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587809341192205120136818139 881714011788307680205227209)
        ·
          refine ⟨661285508841230760153920407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881714011788307680205227209 661285508841230760153920407)
          ·
            refine ⟨991928263261846140230880611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661285508841230760153920407 991928263261846140230880611)
            ·
              refine ⟨1487892394892769210346320917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991928263261846140230880611 1487892394892769210346320917)
              ·
                refine ⟨69744956010598556734983793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1487892394892769210346320917 69744956010598556734983793)
                ·
                  refine ⟨52308717007948917551237845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69744956010598556734983793 52308717007948917551237845)
                  ·
                    refine ⟨1225985554873802755107137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52308717007948917551237845 1225985554873802755107137)
                    ·
                      rfl

theorem cell23_7162795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_7162795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162795 prefixEnd_7162795 := by exact prefixLift 7162795
  have htrace : WordTrace (prefixWord ++ tailWord_7162795) baseStart_7162795 baseEnd_7162795 := by
    simpa [prefixWord, tailWord_7162795, baseEnd_7162795] using wordTrace_append hprefix tailTrace_7162795
  have hstable : (prefixWord ++ tailWord_7162795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162795).length < 2 ^ (prefixWord ++ tailWord_7162795).sum := by decide
  have hdescent : baseEnd_7162795 < baseStart_7162795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162809 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7162809 : Nat := 118140960795 + 7162809 * 2 ^ 59
def prefixEnd_7162809 : Nat := 4983230072969 + 3 ^ 40 * 7162809 * 2
def baseEnd_7162809 : Nat := 3677963853350571210546347

theorem tailTrace_7162809 : CollatzResearch.WordTrace tailWord_7162809 prefixEnd_7162809 3677963853350571210546347 := by
  unfold tailWord_7162809
  simp only [CollatzResearch.WordTrace]
  refine ⟨261249106707373778229595481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174166071138249185486396987 261249106707373778229595481)
  ·
    refine ⟨195936830030530333672196611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261249106707373778229595481 195936830030530333672196611)
    ·
      refine ⟨293905245045795500508294917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195936830030530333672196611 293905245045795500508294917)
      ·
        refine ⟨55107233446086656345305297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293905245045795500508294917 55107233446086656345305297)
        ·
          refine ⟨41330425084564992258978973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55107233446086656345305297 41330425084564992258978973)
          ·
            refine ⟨15498909406711872097117115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41330425084564992258978973 15498909406711872097117115)
            ·
              refine ⟨23248364110067808145675673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15498909406711872097117115 23248364110067808145675673)
              ·
                refine ⟨17436273082550856109256755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23248364110067808145675673 17436273082550856109256755)
                ·
                  refine ⟨26154409623826284163885133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17436273082550856109256755 26154409623826284163885133)
                  ·
                    refine ⟨9807903608934856561456925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26154409623826284163885133 9807903608934856561456925)
                    ·
                      refine ⟨3677963853350571210546347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807903608934856561456925 3677963853350571210546347)
                      ·
                        rfl

theorem cell23_7162809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7162809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162809 prefixEnd_7162809 := by exact prefixLift 7162809
  have htrace : WordTrace (prefixWord ++ tailWord_7162809) baseStart_7162809 baseEnd_7162809 := by
    simpa [prefixWord, tailWord_7162809, baseEnd_7162809] using wordTrace_append hprefix tailTrace_7162809
  have hstable : (prefixWord ++ tailWord_7162809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162809).length < 2 ^ (prefixWord ++ tailWord_7162809).sum := by decide
  have hdescent : baseEnd_7162809 < baseStart_7162809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162813 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_7162813 : Nat := 118140960795 + 7162813 * 2 ^ 59
def prefixEnd_7162813 : Nat := 4983230072969 + 3 ^ 40 * 7162813 * 2
def baseEnd_7162813 : Nat := 3677965907273189194896329

theorem tailTrace_7162813 : CollatzResearch.WordTrace tailWord_7162813 prefixEnd_7162813 3677965907273189194896329 := by
  unfold tailWord_7162813
  simp only [CollatzResearch.WordTrace]
  refine ⟨261249252599359286912741093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174166168399572857941827395 261249252599359286912741093)
  ·
    refine ⟨48984234862379866296138955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261249252599359286912741093 48984234862379866296138955)
    ·
      refine ⟨73476352293569799444208433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48984234862379866296138955 73476352293569799444208433)
      ·
        refine ⟨55107264220177349583156325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73476352293569799444208433 55107264220177349583156325)
        ·
          refine ⟨10332612041283253046841811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55107264220177349583156325 10332612041283253046841811)
          ·
            refine ⟨15498918061924879570262717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332612041283253046841811 15498918061924879570262717)
            ·
              refine ⟨5812094273221829838848519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15498918061924879570262717 5812094273221829838848519)
              ·
                refine ⟨8718141409832744758272779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812094273221829838848519 8718141409832744758272779)
                ·
                  refine ⟨13077212114749117137409169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718141409832744758272779 13077212114749117137409169)
                  ·
                    refine ⟨9807909086061837853056877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13077212114749117137409169 9807909086061837853056877)
                    ·
                      refine ⟨3677965907273189194896329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9807909086061837853056877 3677965907273189194896329)
                      ·
                        rfl

theorem cell23_7162813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_7162813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162813 prefixEnd_7162813 := by exact prefixLift 7162813
  have htrace : WordTrace (prefixWord ++ tailWord_7162813) baseStart_7162813 baseEnd_7162813 := by
    simpa [prefixWord, tailWord_7162813, baseEnd_7162813] using wordTrace_append hprefix tailTrace_7162813
  have hstable : (prefixWord ++ tailWord_7162813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162813).length < 2 ^ (prefixWord ++ tailWord_7162813).sum := by decide
  have hdescent : baseEnd_7162813 < baseStart_7162813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162836 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7162836 : Nat := 118140960795 + 7162836 * 2 ^ 59
def prefixEnd_7162836 : Nat := 4983230072969 + 3 ^ 40 * 7162836 * 2
def baseEnd_7162836 : Nat := 3677977717328242604908723

theorem tailTrace_7162836 : CollatzResearch.WordTrace tailWord_7162836 prefixEnd_7162836 3677977717328242604908723 := by
  unfold tailWord_7162836
  simp only [CollatzResearch.WordTrace]
  refine ⟨130625045739137980920414181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174166727652183974560552241 130625045739137980920414181)
  ·
    refine ⟨24492196076088371422577659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130625045739137980920414181 24492196076088371422577659)
    ·
      refine ⟨36738294114132557133866489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492196076088371422577659 36738294114132557133866489)
      ·
        refine ⟨27553720585599417850399867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36738294114132557133866489 27553720585599417850399867)
        ·
          refine ⟨41330580878399126775599801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27553720585599417850399867 41330580878399126775599801)
          ·
            refine ⟨30997935658799345081699851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41330580878399126775599801 30997935658799345081699851)
            ·
              refine ⟨46496903488199017622549777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30997935658799345081699851 46496903488199017622549777)
              ·
                refine ⟨34872677616149263216912333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46496903488199017622549777 34872677616149263216912333)
                ·
                  refine ⟨13077254106055973706342125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34872677616149263216912333 13077254106055973706342125)
                  ·
                    refine ⟨4903970289770990139878297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13077254106055973706342125 4903970289770990139878297)
                    ·
                      refine ⟨3677977717328242604908723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903970289770990139878297 3677977717328242604908723)
                      ·
                        rfl

theorem cell23_7162836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7162836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162836 prefixEnd_7162836 := by exact prefixLift 7162836
  have htrace : WordTrace (prefixWord ++ tailWord_7162836) baseStart_7162836 baseEnd_7162836 := by
    simpa [prefixWord, tailWord_7162836, baseEnd_7162836] using wordTrace_append hprefix tailTrace_7162836
  have hstable : (prefixWord ++ tailWord_7162836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162836).length < 2 ^ (prefixWord ++ tailWord_7162836).sum := by decide
  have hdescent : baseEnd_7162836 < baseStart_7162836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162842 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_7162842 : Nat := 118140960795 + 7162842 * 2 ^ 59
def prefixEnd_7162842 : Nat := 4983230072969 + 3 ^ 40 * 7162842 * 2
def baseEnd_7162842 : Nat := 1225993599404056527144565

theorem tailTrace_7162842 : CollatzResearch.WordTrace tailWord_7162842 prefixEnd_7162842 1225993599404056527144565 := by
  unfold tailWord_7162842
  simp only [CollatzResearch.WordTrace]
  refine ⟨65312577579063556216386695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174166873544169483243697853 65312577579063556216386695)
  ·
    refine ⟨97968866368595334324580043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65312577579063556216386695 97968866368595334324580043)
    ·
      refine ⟨146953299552893001486870065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97968866368595334324580043 146953299552893001486870065)
      ·
        refine ⟨110214974664669751115152549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146953299552893001486870065 110214974664669751115152549)
        ·
          refine ⟨20665307749625578334091103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110214974664669751115152549 20665307749625578334091103)
          ·
            refine ⟨30997961624438367501136655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665307749625578334091103 30997961624438367501136655)
            ·
              refine ⟨46496942436657551251704983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30997961624438367501136655 46496942436657551251704983)
              ·
                refine ⟨69745413654986326877557475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46496942436657551251704983 69745413654986326877557475)
                ·
                  refine ⟨104618120482479490316336213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69745413654986326877557475 104618120482479490316336213)
                  ·
                    refine ⟨1225993599404056527144565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104618120482479490316336213 1225993599404056527144565)
                    ·
                      rfl

theorem cell23_7162842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_7162842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162842 prefixEnd_7162842 := by exact prefixLift 7162842
  have htrace : WordTrace (prefixWord ++ tailWord_7162842) baseStart_7162842 baseEnd_7162842 := by
    simpa [prefixWord, tailWord_7162842, baseEnd_7162842] using wordTrace_append hprefix tailTrace_7162842
  have hstable : (prefixWord ++ tailWord_7162842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162842).length < 2 ^ (prefixWord ++ tailWord_7162842).sum := by decide
  have hdescent : baseEnd_7162842 < baseStart_7162842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162852 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_7162852 : Nat := 118140960795 + 7162852 * 2 ^ 59
def prefixEnd_7162852 : Nat := 4983230072969 + 3 ^ 40 * 7162852 * 2
def baseEnd_7162852 : Nat := 3677985933018714542308649

theorem tailTrace_7162852 : CollatzResearch.WordTrace tailWord_7162852 prefixEnd_7162852 3677985933018714542308649 := by
  unfold tailWord_7162852
  simp only [CollatzResearch.WordTrace]
  refine ⟨130625337523108998286705405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174167116697478664382273873 130625337523108998286705405)
  ·
    refine ⟨48984501571165874357514527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130625337523108998286705405 48984501571165874357514527)
    ·
      refine ⟨73476752356748811536271791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48984501571165874357514527 73476752356748811536271791)
      ·
        refine ⟨110215128535123217304407687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73476752356748811536271791 110215128535123217304407687)
        ·
          refine ⟨165322692802684825956611531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110215128535123217304407687 165322692802684825956611531)
          ·
            refine ⟨247984039204027238934917297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165322692802684825956611531 247984039204027238934917297)
            ·
              refine ⟨185988029403020429201187973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247984039204027238934917297 185988029403020429201187973)
              ·
                refine ⟨34872755513066330475222745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185988029403020429201187973 34872755513066330475222745)
                ·
                  refine ⟨26154566634799747856417059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34872755513066330475222745 26154566634799747856417059)
                  ·
                    refine ⟨39231849952199621784625589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26154566634799747856417059 39231849952199621784625589)
                    ·
                      refine ⟨3677985933018714542308649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39231849952199621784625589 3677985933018714542308649)
                      ·
                        rfl

theorem cell23_7162852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_7162852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162852 prefixEnd_7162852 := by exact prefixLift 7162852
  have htrace : WordTrace (prefixWord ++ tailWord_7162852) baseStart_7162852 baseEnd_7162852 := by
    simpa [prefixWord, tailWord_7162852, baseEnd_7162852] using wordTrace_append hprefix tailTrace_7162852
  have hstable : (prefixWord ++ tailWord_7162852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162852).length < 2 ^ (prefixWord ++ tailWord_7162852).sum := by decide
  have hdescent : baseEnd_7162852 < baseStart_7162852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162870 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7162870 : Nat := 118140960795 + 7162870 * 2 ^ 59
def prefixEnd_7162870 : Nat := 4983230072969 + 3 ^ 40 * 7162870 * 2
def baseEnd_7162870 : Nat := 3677995175670495471883567

theorem tailTrace_7162870 : CollatzResearch.WordTrace tailWord_7162870 prefixEnd_7162870 3677995175670495471883567 := by
  unfold tailWord_7162870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328208222509549102972879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174167554373435190431710709 16328208222509549102972879)
  ·
    refine ⟨24492312333764323654459319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16328208222509549102972879 24492312333764323654459319)
    ·
      refine ⟨36738468500646485481688979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24492312333764323654459319 36738468500646485481688979)
      ·
        refine ⟨55107702750969728222533469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36738468500646485481688979 55107702750969728222533469)
        ·
          refine ⟨20665388531613648083450051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55107702750969728222533469 20665388531613648083450051)
          ·
            refine ⟨30998082797420472125175077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665388531613648083450051 30998082797420472125175077)
            ·
              refine ⟨5812140524516338523470327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30998082797420472125175077 5812140524516338523470327)
              ·
                refine ⟨8718210786774507785205491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812140524516338523470327 8718210786774507785205491)
                ·
                  refine ⟨13077316180161761677808237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8718210786774507785205491 13077316180161761677808237)
                  ·
                    refine ⟨4903993567560660629178089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13077316180161761677808237 4903993567560660629178089)
                    ·
                      refine ⟨3677995175670495471883567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4903993567560660629178089 3677995175670495471883567)
                      ·
                        rfl

theorem cell23_7162870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7162870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162870 prefixEnd_7162870 := by exact prefixLift 7162870
  have htrace : WordTrace (prefixWord ++ tailWord_7162870) baseStart_7162870 baseEnd_7162870 := by
    simpa [prefixWord, tailWord_7162870, baseEnd_7162870] using wordTrace_append hprefix tailTrace_7162870
  have hstable : (prefixWord ++ tailWord_7162870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162870).length < 2 ^ (prefixWord ++ tailWord_7162870).sum := by decide
  have hdescent : baseEnd_7162870 < baseStart_7162870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7162976 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_7162976 : Nat := 118140960795 + 7162976 * 2 ^ 59
def prefixEnd_7162976 : Nat := 4983230072969 + 3 ^ 40 * 7162976 * 2
def baseEnd_7162976 : Nat := 3678049604619872057158079

theorem tailTrace_7162976 : CollatzResearch.WordTrace tailWord_7162976 prefixEnd_7162976 3678049604619872057158079 := by
  unfold tailWord_7162976
  simp only [CollatzResearch.WordTrace]
  refine ⟨130627598848884382875462391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174170131798512510500616521 130627598848884382875462391)
  ·
    refine ⟨195941398273326574313193587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130627598848884382875462391 195941398273326574313193587)
    ·
      refine ⟨293912097409989861469790381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195941398273326574313193587 293912097409989861469790381)
      ·
        refine ⟨110217036528746198051171393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293912097409989861469790381 110217036528746198051171393)
        ·
          refine ⟨82662777396559648538378545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110217036528746198051171393 82662777396559648538378545)
          ·
            refine ⟨61997083047419736403783909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82662777396559648538378545 61997083047419736403783909)
            ·
              refine ⟨11624453071391200575709483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61997083047419736403783909 11624453071391200575709483)
              ·
                refine ⟨17436679607086800863564225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11624453071391200575709483 17436679607086800863564225)
                ·
                  refine ⟨13077509705315100647673169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17436679607086800863564225 13077509705315100647673169)
                  ·
                    refine ⟨9808132278986325485754877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13077509705315100647673169 9808132278986325485754877)
                    ·
                      refine ⟨3678049604619872057158079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9808132278986325485754877 3678049604619872057158079)
                      ·
                        rfl

theorem cell23_7162976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_7162976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7162976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7162976 prefixEnd_7162976 := by exact prefixLift 7162976
  have htrace : WordTrace (prefixWord ++ tailWord_7162976) baseStart_7162976 baseEnd_7162976 := by
    simpa [prefixWord, tailWord_7162976, baseEnd_7162976] using wordTrace_append hprefix tailTrace_7162976
  have hstable : (prefixWord ++ tailWord_7162976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7162976).length < 2 ^ (prefixWord ++ tailWord_7162976).sum := by decide
  have hdescent : baseEnd_7162976 < baseStart_7162976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7162976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163026 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7163026 : Nat := 118140960795 + 7163026 * 2 ^ 59
def prefixEnd_7163026 : Nat := 4983230072969 + 3 ^ 40 * 7163026 * 2
def baseEnd_7163026 : Nat := 1226025092884198953844283

theorem tailTrace_7163026 : CollatzResearch.WordTrace tailWord_7163026 prefixEnd_7163026 1226025092884198953844283 := by
  unfold tailWord_7163026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65314255336896906072561233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174171347565058416193496621 65314255336896906072561233)
  ·
    refine ⟨48985691502672679554420925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65314255336896906072561233 48985691502672679554420925)
    ·
      refine ⟨18369634313502254832907847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48985691502672679554420925 18369634313502254832907847)
      ·
        refine ⟨27554451470253382249361771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18369634313502254832907847 27554451470253382249361771)
        ·
          refine ⟨41331677205380073374042657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27554451470253382249361771 41331677205380073374042657)
          ·
            refine ⟨30998757904035055030531993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41331677205380073374042657 30998757904035055030531993)
            ·
              refine ⟨23249068428026291272898995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30998757904035055030531993 23249068428026291272898995)
              ·
                refine ⟨34873602642039436909348493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23249068428026291272898995 34873602642039436909348493)
                ·
                  refine ⟨13077600990764788841005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34873602642039436909348493 13077600990764788841005685)
                  ·
                    refine ⟨1226025092884198953844283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13077600990764788841005685 1226025092884198953844283)
                    ·
                      rfl

theorem cell23_7163026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7163026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163026 prefixEnd_7163026 := by exact prefixLift 7163026
  have htrace : WordTrace (prefixWord ++ tailWord_7163026) baseStart_7163026 baseEnd_7163026 := by
    simpa [prefixWord, tailWord_7163026, baseEnd_7163026] using wordTrace_append hprefix tailTrace_7163026
  have hstable : (prefixWord ++ tailWord_7163026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163026).length < 2 ^ (prefixWord ++ tailWord_7163026).sum := by decide
  have hdescent : baseEnd_7163026 < baseStart_7163026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163040 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 1, 1, 3]
def baseStart_7163040 : Nat := 118140960795 + 7163040 * 2 ^ 59
def prefixEnd_7163040 : Nat := 4983230072969 + 3 ^ 40 * 7163040 * 2
def baseEnd_7163040 : Nat := 3678082467381759806757785

theorem tailTrace_7163040 : CollatzResearch.WordTrace tailWord_7163040 prefixEnd_7163040 3678082467381759806757785 := by
  unfold tailWord_7163040
  simp only [CollatzResearch.WordTrace]
  refine ⟨130628765984768452340627287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174171687979691269787503049 130628765984768452340627287)
  ·
    refine ⟨195943148977152678510940931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130628765984768452340627287 195943148977152678510940931)
    ·
      refine ⟨293914723465729017766411397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195943148977152678510940931 293914723465729017766411397)
      ·
        refine ⟨55109010649824190831202137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293914723465729017766411397 55109010649824190831202137)
        ·
          refine ⟨41331757987368143123401603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55109010649824190831202137 41331757987368143123401603)
          ·
            refine ⟨61997636981052214685102405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41331757987368143123401603 61997636981052214685102405)
            ·
              refine ⟨11624556933947290253456701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61997636981052214685102405 11624556933947290253456701)
              ·
                refine ⟨4359208850230233845046263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11624556933947290253456701 4359208850230233845046263)
                ·
                  refine ⟨6538813275345350767569395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359208850230233845046263 6538813275345350767569395)
                  ·
                    refine ⟨9808219913018026151354093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538813275345350767569395 9808219913018026151354093)
                    ·
                      refine ⟨3678082467381759806757785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9808219913018026151354093 3678082467381759806757785)
                      ·
                        rfl

theorem cell23_7163040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_7163040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163040 prefixEnd_7163040 := by exact prefixLift 7163040
  have htrace : WordTrace (prefixWord ++ tailWord_7163040) baseStart_7163040 baseEnd_7163040 := by
    simpa [prefixWord, tailWord_7163040, baseEnd_7163040] using wordTrace_append hprefix tailTrace_7163040
  have hstable : (prefixWord ++ tailWord_7163040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163040).length < 2 ^ (prefixWord ++ tailWord_7163040).sum := by decide
  have hdescent : baseEnd_7163040 < baseStart_7163040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163059 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_7163059 : Nat := 118140960795 + 7163059 * 2 ^ 59
def prefixEnd_7163059 : Nat := 4983230072969 + 3 ^ 40 * 7163059 * 2
def baseEnd_7163059 : Nat := 3678092223514195232420197

theorem tailTrace_7163059 : CollatzResearch.WordTrace tailWord_7163059 prefixEnd_7163059 3678092223514195232420197 := by
  unfold tailWord_7163059
  simp only [CollatzResearch.WordTrace]
  refine ⟨261258224956468070926196231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174172149970978713950797487 261258224956468070926196231)
  ·
    refine ⟨391887337434702106389294347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261258224956468070926196231 391887337434702106389294347)
    ·
      refine ⟨587831006152053159583941521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391887337434702106389294347 587831006152053159583941521)
      ·
        refine ⟨440873254614039869687956141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587831006152053159583941521 440873254614039869687956141)
        ·
          refine ⟨165327470480264951132983553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440873254614039869687956141 165327470480264951132983553)
          ·
            refine ⟨123995602860198713349737665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165327470480264951132983553 123995602860198713349737665)
            ·
              refine ⟨92996702145149035012303249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123995602860198713349737665 92996702145149035012303249)
              ·
                refine ⟨69747526608861776259227437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92996702145149035012303249 69747526608861776259227437)
                ·
                  refine ⟨26155322478323166097210289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69747526608861776259227437 26155322478323166097210289)
                  ·
                    refine ⟨19616491858742374572907717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26155322478323166097210289 19616491858742374572907717)
                    ·
                      refine ⟨3678092223514195232420197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19616491858742374572907717 3678092223514195232420197)
                      ·
                        rfl

theorem cell23_7163059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_7163059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163059 prefixEnd_7163059 := by exact prefixLift 7163059
  have htrace : WordTrace (prefixWord ++ tailWord_7163059) baseStart_7163059 baseEnd_7163059 := by
    simpa [prefixWord, tailWord_7163059, baseEnd_7163059] using wordTrace_append hprefix tailTrace_7163059
  have hstable : (prefixWord ++ tailWord_7163059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163059).length < 2 ^ (prefixWord ++ tailWord_7163059).sum := by decide
  have hdescent : baseEnd_7163059 < baseStart_7163059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163073 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7163073 : Nat := 118140960795 + 7163073 * 2 ^ 59
def prefixEnd_7163073 : Nat := 4983230072969 + 3 ^ 40 * 7163073 * 2
def baseEnd_7163073 : Nat := 1226033137414452725881711

theorem tailTrace_7163073 : CollatzResearch.WordTrace tailWord_7163073 prefixEnd_7163073 1226033137414452725881711 := by
  unfold tailWord_7163073
  simp only [CollatzResearch.WordTrace]
  refine ⟨261258735578417351317205873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174172490385611567544803915 261258735578417351317205873)
  ·
    refine ⟨195944051683813013487904405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261258735578417351317205873 195944051683813013487904405)
    ·
      refine ⟨9184877422678735007245519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195944051683813013487904405 9184877422678735007245519)
      ·
        refine ⟨13777316134018102510868279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184877422678735007245519 13777316134018102510868279)
        ·
          refine ⟨20665974201027153766302419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13777316134018102510868279 20665974201027153766302419)
          ·
            refine ⟨30998961301540730649453629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665974201027153766302419 30998961301540730649453629)
            ·
              refine ⟨11624610488077773993545111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30998961301540730649453629 11624610488077773993545111)
              ·
                refine ⟨17436915732116660990317667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11624610488077773993545111 17436915732116660990317667)
                ·
                  refine ⟨26155373598174991485476501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17436915732116660990317667 26155373598174991485476501)
                  ·
                    refine ⟨1226033137414452725881711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26155373598174991485476501 1226033137414452725881711)
                    ·
                      rfl

theorem cell23_7163073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7163073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163073 prefixEnd_7163073 := by exact prefixLift 7163073
  have htrace : WordTrace (prefixWord ++ tailWord_7163073) baseStart_7163073 baseEnd_7163073 := by
    simpa [prefixWord, tailWord_7163073, baseEnd_7163073] using wordTrace_append hprefix tailTrace_7163073
  have hstable : (prefixWord ++ tailWord_7163073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163073).length < 2 ^ (prefixWord ++ tailWord_7163073).sum := by decide
  have hdescent : baseEnd_7163073 < baseStart_7163073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163086 : List Nat := [4, 1, 1, 1, 5, 1, 1, 9]
def baseStart_7163086 : Nat := 118140960795 + 7163086 * 2 ^ 59
def prefixEnd_7163086 : Nat := 4983230072969 + 3 ^ 40 * 7163086 * 2
def baseEnd_7163086 : Nat := 136226151388587652843799

theorem tailTrace_7163086 : CollatzResearch.WordTrace tailWord_7163086 prefixEnd_7163086 136226151388587652843799 := by
  unfold tailWord_7163086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657401215921281817178639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174172806484913503024952741 32657401215921281817178639)
  ·
    refine ⟨48986101823881922725767959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32657401215921281817178639 48986101823881922725767959)
    ·
      refine ⟨73479152735822884088651939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48986101823881922725767959 73479152735822884088651939)
      ·
        refine ⟨110218729103734326132977909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73479152735822884088651939 110218729103734326132977909)
        ·
          refine ⟨10333005853475093074966679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110218729103734326132977909 10333005853475093074966679)
          ·
            refine ⟨15499508780212639612450019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333005853475093074966679 15499508780212639612450019)
            ·
              refine ⟨23249263170318959418675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499508780212639612450019 23249263170318959418675029)
              ·
                refine ⟨136226151388587652843799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23249263170318959418675029 136226151388587652843799)
                ·
                  rfl

theorem cell23_7163086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_7163086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163086 prefixEnd_7163086 := by exact prefixLift 7163086
  have htrace : WordTrace (prefixWord ++ tailWord_7163086) baseStart_7163086 baseEnd_7163086 := by
    simpa [prefixWord, tailWord_7163086, baseEnd_7163086] using wordTrace_append hprefix tailTrace_7163086
  have hstable : (prefixWord ++ tailWord_7163086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163086).length < 2 ^ (prefixWord ++ tailWord_7163086).sum := by decide
  have hdescent : baseEnd_7163086 < baseStart_7163086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163114 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_7163114 : Nat := 118140960795 + 7163114 * 2 ^ 59
def prefixEnd_7163114 : Nat := 4983230072969 + 3 ^ 40 * 7163114 * 2
def baseEnd_7163114 : Nat := 3678120464950192517232445

theorem tailTrace_7163114 : CollatzResearch.WordTrace tailWord_7163114 prefixEnd_7163114 3678120464950192517232445 := by
  unfold tailWord_7163114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65315057742817203829862099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174173487314179210212965597 65315057742817203829862099)
  ·
    refine ⟨97972586614225805744793149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65315057742817203829862099 97972586614225805744793149)
    ·
      refine ⟨36739719980334677154297431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97972586614225805744793149 36739719980334677154297431)
      ·
        refine ⟨55109579970502015731446147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36739719980334677154297431 55109579970502015731446147)
        ·
          refine ⟨82664369955753023597169221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55109579970502015731446147 82664369955753023597169221)
          ·
            refine ⟨15499569366703691924469229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82664369955753023597169221 15499569366703691924469229)
            ·
              refine ⟨5812338512513884471675961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15499569366703691924469229 5812338512513884471675961)
              ·
                refine ⟨4359253884385413353756971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812338512513884471675961 4359253884385413353756971)
                ·
                  refine ⟨6538880826578120030635457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359253884385413353756971 6538880826578120030635457)
                  ·
                    refine ⟨4904160619933590022976593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6538880826578120030635457 4904160619933590022976593)
                    ·
                      refine ⟨3678120464950192517232445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904160619933590022976593 3678120464950192517232445)
                      ·
                        rfl

theorem cell23_7163114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_7163114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163114 prefixEnd_7163114 := by exact prefixLift 7163114
  have htrace : WordTrace (prefixWord ++ tailWord_7163114) baseStart_7163114 baseEnd_7163114 := by
    simpa [prefixWord, tailWord_7163114, baseEnd_7163114] using wordTrace_append hprefix tailTrace_7163114
  have hstable : (prefixWord ++ tailWord_7163114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163114).length < 2 ^ (prefixWord ++ tailWord_7163114).sum := by decide
  have hdescent : baseEnd_7163114 < baseStart_7163114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163124 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7163124 : Nat := 118140960795 + 7163124 * 2 ^ 59
def prefixEnd_7163124 : Nat := 4983230072969 + 3 ^ 40 * 7163124 * 2
def baseEnd_7163124 : Nat := 1226041866585579159369133

theorem tailTrace_7163124 : CollatzResearch.WordTrace tailWord_7163124 prefixEnd_7163124 1226041866585579159369133 := by
  unfold tailWord_7163124
  simp only [CollatzResearch.WordTrace]
  refine ⟨130630297850616293513656213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174173730467488391351541617 130630297850616293513656213)
  ·
    refine ⟨6123295211747638758452635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130630297850616293513656213 6123295211747638758452635)
    ·
      refine ⟨9184942817621458137678953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6123295211747638758452635 9184942817621458137678953)
      ·
        refine ⟨6888707113216093603259215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9184942817621458137678953 6888707113216093603259215)
        ·
          refine ⟨10333060669824140404888823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888707113216093603259215 10333060669824140404888823)
          ·
            refine ⟨15499591004736210607333235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333060669824140404888823 15499591004736210607333235)
            ·
              refine ⟨23249386507104315910999853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499591004736210607333235 23249386507104315910999853)
              ·
                refine ⟨8718519940164118466624945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23249386507104315910999853 8718519940164118466624945)
                ·
                  refine ⟨6538889955123088849968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718519940164118466624945 6538889955123088849968709)
                  ·
                    refine ⟨1226041866585579159369133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6538889955123088849968709 1226041866585579159369133)
                    ·
                      rfl

theorem cell23_7163124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7163124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163124 prefixEnd_7163124 := by exact prefixLift 7163124
  have htrace : WordTrace (prefixWord ++ tailWord_7163124) baseStart_7163124 baseEnd_7163124 := by
    simpa [prefixWord, tailWord_7163124, baseEnd_7163124] using wordTrace_append hprefix tailTrace_7163124
  have hstable : (prefixWord ++ tailWord_7163124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163124).length < 2 ^ (prefixWord ++ tailWord_7163124).sum := by decide
  have hdescent : baseEnd_7163124 < baseStart_7163124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163129 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_7163129 : Nat := 118140960795 + 7163129 * 2 ^ 59
def prefixEnd_7163129 : Nat := 4983230072969 + 3 ^ 40 * 7163129 * 2
def baseEnd_7163129 : Nat := 1226042722386669986181625

theorem tailTrace_7163129 : CollatzResearch.WordTrace tailWord_7163129 prefixEnd_7163129 1226042722386669986181625 := by
  unfold tailWord_7163129
  simp only [CollatzResearch.WordTrace]
  refine ⟨261260778066214472881244441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174173852044142981920829627 261260778066214472881244441)
  ·
    refine ⟨195945583549660854660933331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261260778066214472881244441 195945583549660854660933331)
    ·
      refine ⟨293918375324491281991399997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195945583549660854660933331 293918375324491281991399997)
      ·
        refine ⟨110219390746684230746774999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293918375324491281991399997 110219390746684230746774999)
        ·
          refine ⟨165329086120026346120162499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110219390746684230746774999 165329086120026346120162499)
          ·
            refine ⟨247993629180039519180243749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165329086120026346120162499 247993629180039519180243749)
            ·
              refine ⟨46498805471257409846295703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247993629180039519180243749 46498805471257409846295703)
              ·
                refine ⟨69748208206886114769443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46498805471257409846295703 69748208206886114769443555)
                ·
                  refine ⟨104622312310329172154165333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69748208206886114769443555 104622312310329172154165333)
                  ·
                    refine ⟨1226042722386669986181625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104622312310329172154165333 1226042722386669986181625)
                    ·
                      rfl

theorem cell23_7163129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_7163129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163129 prefixEnd_7163129 := by exact prefixLift 7163129
  have htrace : WordTrace (prefixWord ++ tailWord_7163129) baseStart_7163129 baseEnd_7163129 := by
    simpa [prefixWord, tailWord_7163129, baseEnd_7163129] using wordTrace_append hprefix tailTrace_7163129
  have hstable : (prefixWord ++ tailWord_7163129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163129).length < 2 ^ (prefixWord ++ tailWord_7163129).sum := by decide
  have hdescent : baseEnd_7163129 < baseStart_7163129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163140 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7163140 : Nat := 118140960795 + 7163140 * 2 ^ 59
def prefixEnd_7163140 : Nat := 4983230072969 + 3 ^ 40 * 7163140 * 2
def baseEnd_7163140 : Nat := 3678133815447209415507325

theorem tailTrace_7163140 : CollatzResearch.WordTrace tailWord_7163140 prefixEnd_7163140 3678133815447209415507325 := by
  unfold tailWord_7163140
  simp only [CollatzResearch.WordTrace]
  refine ⟨130630589634587310879947437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174174119512783081173263249 130630589634587310879947437)
  ·
    refine ⟨48986471112970241579980289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130630589634587310879947437 48986471112970241579980289)
    ·
      refine ⟨36739853334727681184985217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48986471112970241579980289 36739853334727681184985217)
      ·
        refine ⟨27554890001045760888738913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36739853334727681184985217 27554890001045760888738913)
        ·
          refine ⟨20666167500784320666554185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27554890001045760888738913 20666167500784320666554185)
          ·
            refine ⟨15499625625588240499915639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20666167500784320666554185 15499625625588240499915639)
            ·
              refine ⟨23249438438382360749873459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499625625588240499915639 23249438438382360749873459)
              ·
                refine ⟨34874157657573541124810189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23249438438382360749873459 34874157657573541124810189)
                ·
                  refine ⟨13077809121590077921803821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34874157657573541124810189 13077809121590077921803821)
                  ·
                    refine ⟨4904178420596279220676433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13077809121590077921803821 4904178420596279220676433)
                    ·
                      refine ⟨3678133815447209415507325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904178420596279220676433 3678133815447209415507325)
                      ·
                        rfl

theorem cell23_7163140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7163140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163140 prefixEnd_7163140 := by exact prefixLift 7163140
  have htrace : WordTrace (prefixWord ++ tailWord_7163140) baseStart_7163140 baseEnd_7163140 := by
    simpa [prefixWord, tailWord_7163140, baseEnd_7163140] using wordTrace_append hprefix tailTrace_7163140
  have hstable : (prefixWord ++ tailWord_7163140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163140).length < 2 ^ (prefixWord ++ tailWord_7163140).sum := by decide
  have hdescent : baseEnd_7163140 < baseStart_7163140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163153 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_7163153 : Nat := 118140960795 + 7163153 * 2 ^ 59
def prefixEnd_7163153 : Nat := 4983230072969 + 3 ^ 40 * 7163153 * 2
def baseEnd_7163153 : Nat := 3678140490695717864644765

theorem tailTrace_7163153 : CollatzResearch.WordTrace tailWord_7163153 prefixEnd_7163153 3678140490695717864644765 := by
  unfold tailWord_7163153
  simp only [CollatzResearch.WordTrace]
  refine ⟨261261653418127524980118113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174174435612085016653412075 261261653418127524980118113)
  ·
    refine ⟨195946240063595643735088585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261261653418127524980118113 195946240063595643735088585)
    ·
      refine ⟨146959680047696732801316439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195946240063595643735088585 146959680047696732801316439)
      ·
        refine ⟨220439520071545099201974659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146959680047696732801316439 220439520071545099201974659)
        ·
          refine ⟨330659280107317648802961989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220439520071545099201974659 330659280107317648802961989)
          ·
            refine ⟨61998615020122059150555373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330659280107317648802961989 61998615020122059150555373)
            ·
              refine ⟨23249480632545772181458265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61998615020122059150555373 23249480632545772181458265)
              ·
                refine ⟨17437110474409329136093699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23249480632545772181458265 17437110474409329136093699)
                ·
                  refine ⟨26155665711613993704140549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17437110474409329136093699 26155665711613993704140549)
                  ·
                    refine ⟨4904187320927623819526353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26155665711613993704140549 4904187320927623819526353)
                    ·
                      refine ⟨3678140490695717864644765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904187320927623819526353 3678140490695717864644765)
                      ·
                        rfl

theorem cell23_7163153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_7163153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163153 prefixEnd_7163153 := by exact prefixLift 7163153
  have htrace : WordTrace (prefixWord ++ tailWord_7163153) baseStart_7163153 baseEnd_7163153 := by
    simpa [prefixWord, tailWord_7163153, baseEnd_7163153] using wordTrace_append hprefix tailTrace_7163153
  have hstable : (prefixWord ++ tailWord_7163153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163153).length < 2 ^ (prefixWord ++ tailWord_7163153).sum := by decide
  have hdescent : baseEnd_7163153 < baseStart_7163153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163193 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 7]
def baseStart_7163193 : Nat := 118140960795 + 7163193 * 2 ^ 59
def prefixEnd_7163193 : Nat := 4983230072969 + 3 ^ 40 * 7163193 * 2
def baseEnd_7163193 : Nat := 408684558880210856460509

theorem tailTrace_7163193 : CollatzResearch.WordTrace tailWord_7163193 prefixEnd_7163193 408684558880210856460509 := by
  unfold tailWord_7163193
  simp only [CollatzResearch.WordTrace]
  refine ⟨261263112337982611811574233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174175408225321741207716155 261263112337982611811574233)
  ·
    refine ⟨195947334253486958858680675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261263112337982611811574233 195947334253486958858680675)
    ·
      refine ⟨293921001380230438288021013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195947334253486958858680675 293921001380230438288021013)
      ·
        refine ⟨13777546939698301794750985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293921001380230438288021013 13777546939698301794750985)
        ·
          refine ⟨10333160204773726346063239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777546939698301794750985 10333160204773726346063239)
          ·
            refine ⟨15499740307160589519094859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333160204773726346063239 15499740307160589519094859)
            ·
              refine ⟨23249610460740884278642289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499740307160589519094859 23249610460740884278642289)
              ·
                refine ⟨17437207845555663208981717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23249610460740884278642289 17437207845555663208981717)
                ·
                  refine ⟨408684558880210856460509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17437207845555663208981717 408684558880210856460509)
                  ·
                    rfl

theorem cell23_7163193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_7163193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163193 prefixEnd_7163193 := by exact prefixLift 7163193
  have htrace : WordTrace (prefixWord ++ tailWord_7163193) baseStart_7163193 baseEnd_7163193 := by
    simpa [prefixWord, tailWord_7163193, baseEnd_7163193] using wordTrace_append hprefix tailTrace_7163193
  have hstable : (prefixWord ++ tailWord_7163193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163193).length < 2 ^ (prefixWord ++ tailWord_7163193).sum := by decide
  have hdescent : baseEnd_7163193 < baseStart_7163193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163313 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_7163313 : Nat := 118140960795 + 7163313 * 2 ^ 59
def prefixEnd_7163313 : Nat := 4983230072969 + 3 ^ 40 * 7163313 * 2
def baseEnd_7163313 : Nat := 1226074215866812412881343

theorem tailTrace_7163313 : CollatzResearch.WordTrace tailWord_7163313 prefixEnd_7163313 1226074215866812412881343 := by
  unfold tailWord_7163313
  simp only [CollatzResearch.WordTrace]
  refine ⟨261267489097547872305942593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174178326065031914870628395 261267489097547872305942593)
  ·
    refine ⟨195950616823160904229456945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261267489097547872305942593 195950616823160904229456945)
    ·
      refine ⟨146962962617370678172092709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195950616823160904229456945 146962962617370678172092709)
      ·
        refine ⟨27555555490757002157267383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146962962617370678172092709 27555555490757002157267383)
        ·
          refine ⟨41333333236135503235901075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27555555490757002157267383 41333333236135503235901075)
          ·
            refine ⟨61999999854203254853851613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41333333236135503235901075 61999999854203254853851613)
            ·
              refine ⟨23249999945326220570194355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61999999854203254853851613 23249999945326220570194355)
              ·
                refine ⟨34874999917989330855291533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23249999945326220570194355 34874999917989330855291533)
                ·
                  refine ⟨13078124969245999070734325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34874999917989330855291533 13078124969245999070734325)
                  ·
                    refine ⟨1226074215866812412881343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13078124969245999070734325 1226074215866812412881343)
                    ·
                      rfl

theorem cell23_7163313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_7163313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163313 prefixEnd_7163313 := by exact prefixLift 7163313
  have htrace : WordTrace (prefixWord ++ tailWord_7163313) baseStart_7163313 baseEnd_7163313 := by
    simpa [prefixWord, tailWord_7163313, baseEnd_7163313] using wordTrace_append hprefix tailTrace_7163313
  have hstable : (prefixWord ++ tailWord_7163313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163313).length < 2 ^ (prefixWord ++ tailWord_7163313).sum := by decide
  have hdescent : baseEnd_7163313 < baseStart_7163313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163320 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_7163320 : Nat := 118140960795 + 7163320 * 2 ^ 59
def prefixEnd_7163320 : Nat := 4983230072969 + 3 ^ 40 * 7163320 * 2
def baseEnd_7163320 : Nat := 3678226241965018711256497

theorem tailTrace_7163320 : CollatzResearch.WordTrace tailWord_7163320 prefixEnd_7163320 3678226241965018711256497 := by
  unfold tailWord_7163320
  simp only [CollatzResearch.WordTrace]
  refine ⟨130633872204261256250723707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174178496272348341667631609 130633872204261256250723707)
  ·
    refine ⟨195950808306391884376085561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130633872204261256250723707 195950808306391884376085561)
    ·
      refine ⟨146963106229793913282064171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195950808306391884376085561 146963106229793913282064171)
      ·
        refine ⟨220444659344690869923096257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146963106229793913282064171 220444659344690869923096257)
        ·
          refine ⟨165333494508518152442322193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220444659344690869923096257 165333494508518152442322193)
          ·
            refine ⟨124000120881388614331741645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165333494508518152442322193 124000120881388614331741645)
            ·
              refine ⟨46500045330520730374403117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124000120881388614331741645 46500045330520730374403117)
              ·
                refine ⟨17437516998945273890401169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46500045330520730374403117 17437516998945273890401169)
                ·
                  refine ⟨13078137749208955417800877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17437516998945273890401169 13078137749208955417800877)
                  ·
                    refine ⟨4904301655953358281675329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13078137749208955417800877 4904301655953358281675329)
                    ·
                      refine ⟨3678226241965018711256497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904301655953358281675329 3678226241965018711256497)
                      ·
                        rfl

theorem cell23_7163320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_7163320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163320 prefixEnd_7163320 := by exact prefixLift 7163320
  have htrace : WordTrace (prefixWord ++ tailWord_7163320) baseStart_7163320 baseEnd_7163320 := by
    simpa [prefixWord, tailWord_7163320, baseEnd_7163320] using wordTrace_append hprefix tailTrace_7163320
  have hstable : (prefixWord ++ tailWord_7163320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163320).length < 2 ^ (prefixWord ++ tailWord_7163320).sum := by decide
  have hdescent : baseEnd_7163320 < baseStart_7163320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163343 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 4, 4]
def baseStart_7163343 : Nat := 118140960795 + 7163343 * 2 ^ 59
def prefixEnd_7163343 : Nat := 4983230072969 + 3 ^ 40 * 7163343 * 2
def baseEnd_7163343 : Nat := 1226079350673357373756297

theorem tailTrace_7163343 : CollatzResearch.WordTrace tailWord_7163343 prefixEnd_7163343 1226079350673357373756297 := by
  unfold tailWord_7163343
  simp only [CollatzResearch.WordTrace]
  refine ⟨261268583287439187429534683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174179055524959458286356455 261268583287439187429534683)
  ·
    refine ⟨391902874931158781144302025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261268583287439187429534683 391902874931158781144302025)
    ·
      refine ⟨293927156198369085858226519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391902874931158781144302025 293927156198369085858226519)
      ·
        refine ⟨440890734297553628787339779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293927156198369085858226519 440890734297553628787339779)
        ·
          refine ⟨661336101446330443181009669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440890734297553628787339779 661336101446330443181009669)
          ·
            refine ⟨124000519021186958096439313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 661336101446330443181009669 124000519021186958096439313)
            ·
              refine ⟨93000389265890218572329485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124000519021186958096439313 93000389265890218572329485)
              ·
                refine ⟨34875145974708831964623557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93000389265890218572329485 34875145974708831964623557)
                ·
                  refine ⟨6539089870257905993366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34875145974708831964623557 6539089870257905993366917)
                  ·
                    refine ⟨1226079350673357373756297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539089870257905993366917 1226079350673357373756297)
                    ·
                      rfl

theorem cell23_7163343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_7163343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163343 prefixEnd_7163343 := by exact prefixLift 7163343
  have htrace : WordTrace (prefixWord ++ tailWord_7163343) baseStart_7163343 baseEnd_7163343 := by
    simpa [prefixWord, tailWord_7163343, baseEnd_7163343] using wordTrace_append hprefix tailTrace_7163343
  have hstable : (prefixWord ++ tailWord_7163343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163343).length < 2 ^ (prefixWord ++ tailWord_7163343).sum := by decide
  have hdescent : baseEnd_7163343 < baseStart_7163343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163367 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7163367 : Nat := 118140960795 + 7163367 * 2 ^ 59
def prefixEnd_7163367 : Nat := 4983230072969 + 3 ^ 40 * 7163367 * 2
def baseEnd_7163367 : Nat := 3678250375555780027368781

theorem tailTrace_7163367 : CollatzResearch.WordTrace tailWord_7163367 prefixEnd_7163367 3678250375555780027368781 := by
  unfold tailWord_7163367
  simp only [CollatzResearch.WordTrace]
  refine ⟨261269458639352239528408355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174179639092901493018938903 261269458639352239528408355)
  ·
    refine ⟨391904187959028359292612533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261269458639352239528408355 391904187959028359292612533)
    ·
      refine ⟨36741017621158908683682425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391904187959028359292612533 36741017621158908683682425)
      ·
        refine ⟨27555763215869181512761819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36741017621158908683682425 27555763215869181512761819)
        ·
          refine ⟨41333644823803772269142729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27555763215869181512761819 41333644823803772269142729)
          ·
            refine ⟨31000233617852829201857047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41333644823803772269142729 31000233617852829201857047)
            ·
              refine ⟨46500350426779243802785571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31000233617852829201857047 46500350426779243802785571)
              ·
                refine ⟨69750525640168865704178357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46500350426779243802785571 69750525640168865704178357)
                ·
                  refine ⟨6539111778765831159766721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69750525640168865704178357 6539111778765831159766721)
                  ·
                    refine ⟨4904333834074373369825041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6539111778765831159766721 4904333834074373369825041)
                    ·
                      refine ⟨3678250375555780027368781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904333834074373369825041 3678250375555780027368781)
                      ·
                        rfl

theorem cell23_7163367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7163367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163367 prefixEnd_7163367 := by exact prefixLift 7163367
  have htrace : WordTrace (prefixWord ++ tailWord_7163367) baseStart_7163367 baseEnd_7163367 := by
    simpa [prefixWord, tailWord_7163367, baseEnd_7163367] using wordTrace_append hprefix tailTrace_7163367
  have hstable : (prefixWord ++ tailWord_7163367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163367).length < 2 ^ (prefixWord ++ tailWord_7163367).sum := by decide
  have hdescent : baseEnd_7163367 < baseStart_7163367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163383 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_7163383 : Nat := 118140960795 + 7163383 * 2 ^ 59
def prefixEnd_7163383 : Nat := 4983230072969 + 3 ^ 40 * 7163383 * 2
def baseEnd_7163383 : Nat := 3678258591246251964768707

theorem tailTrace_7163383 : CollatzResearch.WordTrace tailWord_7163383 prefixEnd_7163383 3678258591246251964768707 := by
  unfold tailWord_7163383
  simp only [CollatzResearch.WordTrace]
  refine ⟨261270042207294274260990803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174180028138196182840660535 261270042207294274260990803)
  ·
    refine ⟨391905063310941411391486205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261270042207294274260990803 391905063310941411391486205)
    ·
      refine ⟨146964398741603029271807327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391905063310941411391486205 146964398741603029271807327)
      ·
        refine ⟨220446598112404543907710991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146964398741603029271807327 220446598112404543907710991)
        ·
          refine ⟨330669897168606815861566487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220446598112404543907710991 330669897168606815861566487)
          ·
            refine ⟨496004845752910223792349731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330669897168606815861566487 496004845752910223792349731)
            ·
              refine ⟨744007268629365335688524597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496004845752910223792349731 744007268629365335688524597)
              ·
                refine ⟨69750681434003000220799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 744007268629365335688524597 69750681434003000220799181)
                ·
                  refine ⟨26156505537751125082799693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69750681434003000220799181 26156505537751125082799693)
                  ·
                    refine ⟨9808689576656671906049885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26156505537751125082799693 9808689576656671906049885)
                    ·
                      refine ⟨3678258591246251964768707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9808689576656671906049885 3678258591246251964768707)
                      ·
                        rfl

theorem cell23_7163383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_7163383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163383 prefixEnd_7163383 := by exact prefixLift 7163383
  have htrace : WordTrace (prefixWord ++ tailWord_7163383) baseStart_7163383 baseEnd_7163383 := by
    simpa [prefixWord, tailWord_7163383, baseEnd_7163383] using wordTrace_append hprefix tailTrace_7163383
  have hstable : (prefixWord ++ tailWord_7163383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163383).length < 2 ^ (prefixWord ++ tailWord_7163383).sum := by decide
  have hdescent : baseEnd_7163383 < baseStart_7163383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163384 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_7163384 : Nat := 118140960795 + 7163384 * 2 ^ 59
def prefixEnd_7163384 : Nat := 4983230072969 + 3 ^ 40 * 7163384 * 2
def baseEnd_7163384 : Nat := 3678259104726906460856203

theorem tailTrace_7163384 : CollatzResearch.WordTrace tailWord_7163384 prefixEnd_7163384 3678259104726906460856203 := by
  unfold tailWord_7163384
  simp only [CollatzResearch.WordTrace]
  refine ⟨130635039340145325715888603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174180052453527100954518137 130635039340145325715888603)
  ·
    refine ⟨195952559010217988573832905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130635039340145325715888603 195952559010217988573832905)
    ·
      refine ⟨146964419257663491430374679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195952559010217988573832905 146964419257663491430374679)
      ·
        refine ⟨220446628886495237145562019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146964419257663491430374679 220446628886495237145562019)
        ·
          refine ⟨330669943329742855718343029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220446628886495237145562019 330669943329742855718343029)
          ·
            refine ⟨31000307187163392723594659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330669943329742855718343029 31000307187163392723594659)
            ·
              refine ⟨46500460780745089085391989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31000307187163392723594659 46500460780745089085391989)
              ·
                refine ⟨4359418198194852101755499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46500460780745089085391989 4359418198194852101755499)
                ·
                  refine ⟨6539127297292278152633249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359418198194852101755499 6539127297292278152633249)
                  ·
                    refine ⟨4904345472969208614474937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6539127297292278152633249 4904345472969208614474937)
                    ·
                      refine ⟨3678259104726906460856203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904345472969208614474937 3678259104726906460856203)
                      ·
                        rfl

theorem cell23_7163384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_7163384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163384 prefixEnd_7163384 := by exact prefixLift 7163384
  have htrace : WordTrace (prefixWord ++ tailWord_7163384) baseStart_7163384 baseEnd_7163384 := by
    simpa [prefixWord, tailWord_7163384, baseEnd_7163384] using wordTrace_append hprefix tailTrace_7163384
  have hstable : (prefixWord ++ tailWord_7163384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163384).length < 2 ^ (prefixWord ++ tailWord_7163384).sum := by decide
  have hdescent : baseEnd_7163384 < baseStart_7163384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163394 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7163394 : Nat := 118140960795 + 7163394 * 2 ^ 59
def prefixEnd_7163394 : Nat := 4983230072969 + 3 ^ 40 * 7163394 * 2
def baseEnd_7163394 : Nat := 1226088079844483807243719

theorem tailTrace_7163394 : CollatzResearch.WordTrace tailWord_7163394 prefixEnd_7163394 1226088079844483807243719 := by
  unfold tailWord_7163394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65317610852563605784910309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174180295606836282093094157 65317610852563605784910309)
  ·
    refine ⟨12247052034855676084670683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65317610852563605784910309 12247052034855676084670683)
    ·
      refine ⟨18370578052283514127006025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247052034855676084670683 18370578052283514127006025)
      ·
        refine ⟨13777933539212635595254519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18370578052283514127006025 13777933539212635595254519)
        ·
          refine ⟨20666900308818953392881779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13777933539212635595254519 20666900308818953392881779)
          ·
            refine ⟨31000350463228430089322669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20666900308818953392881779 31000350463228430089322669)
            ·
              refine ⟨11625131423710661283496001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31000350463228430089322669 11625131423710661283496001)
              ·
                refine ⟨8718848567782995962622001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11625131423710661283496001 8718848567782995962622001)
                ·
                  refine ⟨6539136425837246971966501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718848567782995962622001 6539136425837246971966501)
                  ·
                    refine ⟨1226088079844483807243719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539136425837246971966501 1226088079844483807243719)
                    ·
                      rfl

theorem cell23_7163394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7163394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163394 prefixEnd_7163394 := by exact prefixLift 7163394
  have htrace : WordTrace (prefixWord ++ tailWord_7163394) baseStart_7163394 baseEnd_7163394 := by
    simpa [prefixWord, tailWord_7163394, baseEnd_7163394] using wordTrace_append hprefix tailTrace_7163394
  have hstable : (prefixWord ++ tailWord_7163394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163394).length < 2 ^ (prefixWord ++ tailWord_7163394).sum := by decide
  have hdescent : baseEnd_7163394 < baseStart_7163394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163423 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_7163423 : Nat := 118140960795 + 7163423 * 2 ^ 59
def prefixEnd_7163423 : Nat := 4983230072969 + 3 ^ 40 * 7163423 * 2
def baseEnd_7163423 : Nat := 3678279130472431808268523

theorem tailTrace_7163423 : CollatzResearch.WordTrace tailWord_7163423 prefixEnd_7163423 3678279130472431808268523 := by
  unfold tailWord_7163423
  simp only [CollatzResearch.WordTrace]
  refine ⟨261271501127149361092446923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174181000751432907394964615 261271501127149361092446923)
  ·
    refine ⟨391907251690724041638670385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261271501127149361092446923 391907251690724041638670385)
    ·
      refine ⟨293930438768043031229002789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391907251690724041638670385 293930438768043031229002789)
      ·
        refine ⟨55111957269008068355438023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293930438768043031229002789 55111957269008068355438023)
        ·
          refine ⟨82667935903512102533157035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55111957269008068355438023 82667935903512102533157035)
          ·
            refine ⟨124001903855268153799735553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82667935903512102533157035 124001903855268153799735553)
            ·
              refine ⟨93001427891451115349801665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124001903855268153799735553 93001427891451115349801665)
              ·
                refine ⟨69751070918588336512351249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93001427891451115349801665 69751070918588336512351249)
                ·
                  refine ⟨52313303188941252384263437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69751070918588336512351249 52313303188941252384263437)
                  ·
                    refine ⟨19617488695852969644098789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52313303188941252384263437 19617488695852969644098789)
                    ·
                      refine ⟨3678279130472431808268523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19617488695852969644098789 3678279130472431808268523)
                      ·
                        rfl

theorem cell23_7163423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_7163423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163423 prefixEnd_7163423 := by exact prefixLift 7163423
  have htrace : WordTrace (prefixWord ++ tailWord_7163423) baseStart_7163423 baseEnd_7163423 := by
    simpa [prefixWord, tailWord_7163423, baseEnd_7163423] using wordTrace_append hprefix tailTrace_7163423
  have hstable : (prefixWord ++ tailWord_7163423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163423).length < 2 ^ (prefixWord ++ tailWord_7163423).sum := by decide
  have hdescent : baseEnd_7163423 < baseStart_7163423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163440 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2]
def baseStart_7163440 : Nat := 118140960795 + 7163440 * 2 ^ 59
def prefixEnd_7163440 : Nat := 4983230072969 + 3 ^ 40 * 7163440 * 2
def baseEnd_7163440 : Nat := 3678287859643558241755945

theorem tailTrace_7163440 : CollatzResearch.WordTrace tailWord_7163440 prefixEnd_7163440 3678287859643558241755945 := by
  unfold tailWord_7163440
  simp only [CollatzResearch.WordTrace]
  refine ⟨130636060584043886497907887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174181414112058515330543849 130636060584043886497907887)
  ·
    refine ⟨195954090876065829746861831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130636060584043886497907887 195954090876065829746861831)
    ·
      refine ⟨293931136314098744620292747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195954090876065829746861831 293931136314098744620292747)
      ·
        refine ⟨440896704471148116930439121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293931136314098744620292747 440896704471148116930439121)
        ·
          refine ⟨330672528353361087697829341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440896704471148116930439121 330672528353361087697829341)
          ·
            refine ⟨124002198132510407886686003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330672528353361087697829341 124002198132510407886686003)
            ·
              refine ⟨186003297198765611830029005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124002198132510407886686003 186003297198765611830029005)
              ·
                refine ⟨69751236449537104436260877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186003297198765611830029005 69751236449537104436260877)
                ·
                  refine ⟨26156713668576414163597829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69751236449537104436260877 26156713668576414163597829)
                  ·
                    refine ⟨4904383812858077655674593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26156713668576414163597829 4904383812858077655674593)
                    ·
                      refine ⟨3678287859643558241755945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904383812858077655674593 3678287859643558241755945)
                      ·
                        rfl

theorem cell23_7163440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2].length) (baseStart_7163440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163440 prefixEnd_7163440 := by exact prefixLift 7163440
  have htrace : WordTrace (prefixWord ++ tailWord_7163440) baseStart_7163440 baseEnd_7163440 := by
    simpa [prefixWord, tailWord_7163440, baseEnd_7163440] using wordTrace_append hprefix tailTrace_7163440
  have hstable : (prefixWord ++ tailWord_7163440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163440).length < 2 ^ (prefixWord ++ tailWord_7163440).sum := by decide
  have hdescent : baseEnd_7163440 < baseStart_7163440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163443 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_7163443 : Nat := 118140960795 + 7163443 * 2 ^ 59
def prefixEnd_7163443 : Nat := 4983230072969 + 3 ^ 40 * 7163443 * 2
def baseEnd_7163443 : Nat := 3678289400085521730018431

theorem tailTrace_7163443 : CollatzResearch.WordTrace tailWord_7163443 prefixEnd_7163443 3678289400085521730018431 := by
  unfold tailWord_7163443
  simp only [CollatzResearch.WordTrace]
  refine ⟨261272230587076904508174983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174181487058051269672116655 261272230587076904508174983)
  ·
    refine ⟨391908345880615356762262475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261272230587076904508174983 391908345880615356762262475)
    ·
      refine ⟨587862518820923035143393713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391908345880615356762262475 587862518820923035143393713)
      ·
        refine ⟨440896889115692276357545285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587862518820923035143393713 440896889115692276357545285)
        ·
          refine ⟨82668166709192301817039741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440896889115692276357545285 82668166709192301817039741)
          ·
            refine ⟨31000562515947113181389903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82668166709192301817039741 31000562515947113181389903)
            ·
              refine ⟨46500843773920669772084855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31000562515947113181389903 46500843773920669772084855)
              ·
                refine ⟨69751265660881004658127283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46500843773920669772084855 69751265660881004658127283)
                ·
                  refine ⟨104626898491321506987190925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69751265660881004658127283 104626898491321506987190925)
                  ·
                    refine ⟨39235086934245565120196597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104626898491321506987190925 39235086934245565120196597)
                    ·
                      refine ⟨3678289400085521730018431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39235086934245565120196597 3678289400085521730018431)
                      ·
                        rfl

theorem cell23_7163443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_7163443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163443 prefixEnd_7163443 := by exact prefixLift 7163443
  have htrace : WordTrace (prefixWord ++ tailWord_7163443) baseStart_7163443 baseEnd_7163443 := by
    simpa [prefixWord, tailWord_7163443, baseEnd_7163443] using wordTrace_append hprefix tailTrace_7163443
  have hstable : (prefixWord ++ tailWord_7163443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163443).length < 2 ^ (prefixWord ++ tailWord_7163443).sum := by decide
  have hdescent : baseEnd_7163443 < baseStart_7163443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163478 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7163478 : Nat := 118140960795 + 7163478 * 2 ^ 59
def prefixEnd_7163478 : Nat := 4983230072969 + 3 ^ 40 * 7163478 * 2
def baseEnd_7163478 : Nat := 3678307371908429093080771

theorem tailTrace_7163478 : CollatzResearch.WordTrace tailWord_7163478 prefixEnd_7163478 3678307371908429093080771 := by
  unfold tailWord_7163478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16329594196371881592856193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174182338094633403657132725 16329594196371881592856193)
  ·
    refine ⟨12247195647278911194642145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16329594196371881592856193 12247195647278911194642145)
    ·
      refine ⟨9185396735459183395981609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12247195647278911194642145 9185396735459183395981609)
      ·
        refine ⟨6889047551594387546986207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9185396735459183395981609 6889047551594387546986207)
        ·
          refine ⟨10333571327391581320479311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6889047551594387546986207 10333571327391581320479311)
          ·
            refine ⟨15500356991087371980718967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10333571327391581320479311 15500356991087371980718967)
            ·
              refine ⟨23250535486631057971078451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15500356991087371980718967 23250535486631057971078451)
              ·
                refine ⟨34875803229946586956617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23250535486631057971078451 34875803229946586956617677)
                ·
                  refine ⟨13078426211229970108731629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34875803229946586956617677 13078426211229970108731629)
                  ·
                    refine ⟨4904409829211238790774361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13078426211229970108731629 4904409829211238790774361)
                    ·
                      refine ⟨3678307371908429093080771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904409829211238790774361 3678307371908429093080771)
                      ·
                        rfl

theorem cell23_7163478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7163478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163478 prefixEnd_7163478 := by exact prefixLift 7163478
  have htrace : WordTrace (prefixWord ++ tailWord_7163478) baseStart_7163478 baseEnd_7163478 := by
    simpa [prefixWord, tailWord_7163478, baseEnd_7163478] using wordTrace_append hprefix tailTrace_7163478
  have hstable : (prefixWord ++ tailWord_7163478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163478).length < 2 ^ (prefixWord ++ tailWord_7163478).sum := by decide
  have hdescent : baseEnd_7163478 < baseStart_7163478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163517 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_7163517 : Nat := 118140960795 + 7163517 * 2 ^ 59
def prefixEnd_7163517 : Nat := 4983230072969 + 3 ^ 40 * 7163517 * 2
def baseEnd_7163517 : Nat := 3678327397653954440493091

theorem tailTrace_7163517 : CollatzResearch.WordTrace tailWord_7163517 prefixEnd_7163517 3678327397653954440493091 := by
  unfold tailWord_7163517
  simp only [CollatzResearch.WordTrace]
  refine ⟨261274929588808815146368805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174183286392539210097579203 261274929588808815146368805)
  ·
    refine ⟨48989049297901652839944151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261274929588808815146368805 48989049297901652839944151)
    ·
      refine ⟨73483573946852479259916227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48989049297901652839944151 73483573946852479259916227)
      ·
        refine ⟨110225360920278718889874341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73483573946852479259916227 110225360920278718889874341)
        ·
          refine ⟨20667255172552259791851439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110225360920278718889874341 20667255172552259791851439)
          ·
            refine ⟨31000882758828389687777159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20667255172552259791851439 31000882758828389687777159)
            ·
              refine ⟨46501324138242584531665739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31000882758828389687777159 46501324138242584531665739)
              ·
                refine ⟨69751986207363876797498609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46501324138242584531665739 69751986207363876797498609)
                ·
                  refine ⟨52313989655522907598123957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69751986207363876797498609 52313989655522907598123957)
                  ·
                    refine ⟨4904436530205272587324121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52313989655522907598123957 4904436530205272587324121)
                    ·
                      refine ⟨3678327397653954440493091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904436530205272587324121 3678327397653954440493091)
                      ·
                        rfl

theorem cell23_7163517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_7163517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163517 prefixEnd_7163517 := by exact prefixLift 7163517
  have htrace : WordTrace (prefixWord ++ tailWord_7163517) baseStart_7163517 baseEnd_7163517 := by
    simpa [prefixWord, tailWord_7163517, baseEnd_7163517] using wordTrace_append hprefix tailTrace_7163517
  have hstable : (prefixWord ++ tailWord_7163517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163517).length < 2 ^ (prefixWord ++ tailWord_7163517).sum := by decide
  have hdescent : baseEnd_7163517 < baseStart_7163517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163523 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 8]
def baseStart_7163523 : Nat := 118140960795 + 7163523 * 2 ^ 59
def prefixEnd_7163523 : Nat := 4983230072969 + 3 ^ 40 * 7163523 * 2
def baseEnd_7163523 : Nat := 1226110159512627139006021

theorem tailTrace_7163523 : CollatzResearch.WordTrace tailWord_7163523 prefixEnd_7163523 1226110159512627139006021 := by
  unfold tailWord_7163523
  simp only [CollatzResearch.WordTrace]
  refine ⟨261275148426787078171087223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174183432284524718780724815 261275148426787078171087223)
  ·
    refine ⟨391912722640180617256630835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261275148426787078171087223 391912722640180617256630835)
    ·
      refine ⟨587869083960270925884946253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391912722640180617256630835 587869083960270925884946253)
      ·
        refine ⟨220450906485101597206854845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587869083960270925884946253 220450906485101597206854845)
        ·
          refine ⟨82669089931913098952570567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220450906485101597206854845 82669089931913098952570567)
          ·
            refine ⟨124003634897869648428855851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82669089931913098952570567 124003634897869648428855851)
            ·
              refine ⟨186005452346804472643283777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124003634897869648428855851 186005452346804472643283777)
              ·
                refine ⟨139504089260103354482462833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186005452346804472643283777 139504089260103354482462833)
                ·
                  refine ⟨104628066945077515861847125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139504089260103354482462833 104628066945077515861847125)
                  ·
                    refine ⟨1226110159512627139006021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104628066945077515861847125 1226110159512627139006021)
                    ·
                      rfl

theorem cell23_7163523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_7163523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163523 prefixEnd_7163523 := by exact prefixLift 7163523
  have htrace : WordTrace (prefixWord ++ tailWord_7163523) baseStart_7163523 baseEnd_7163523 := by
    simpa [prefixWord, tailWord_7163523, baseEnd_7163523] using wordTrace_append hprefix tailTrace_7163523
  have hstable : (prefixWord ++ tailWord_7163523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163523).length < 2 ^ (prefixWord ++ tailWord_7163523).sum := by decide
  have hdescent : baseEnd_7163523 < baseStart_7163523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163563 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_7163563 : Nat := 118140960795 + 7163563 * 2 ^ 59
def prefixEnd_7163563 : Nat := 4983230072969 + 3 ^ 40 * 7163563 * 2
def baseEnd_7163563 : Nat := 3678351017764061260517879

theorem tailTrace_7163563 : CollatzResearch.WordTrace tailWord_7163563 prefixEnd_7163563 3678351017764061260517879 := by
  unfold tailWord_7163563
  simp only [CollatzResearch.WordTrace]
  refine ⟨261276607346642165002543343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174184404897761443335028895 261276607346642165002543343)
  ·
    refine ⟨391914911019963247503815015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261276607346642165002543343 391914911019963247503815015)
    ·
      refine ⟨587872366529944871255722523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391914911019963247503815015 587872366529944871255722523)
      ·
        refine ⟨881808549794917306883583785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587872366529944871255722523 881808549794917306883583785)
        ·
          refine ⟨661356412346187980162687839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881808549794917306883583785 661356412346187980162687839)
          ·
            refine ⟨992034618519281970244031759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661356412346187980162687839 992034618519281970244031759)
            ·
              refine ⟨1488051927778922955366047639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992034618519281970244031759 1488051927778922955366047639)
              ·
                refine ⟨2232077891668384433049071459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488051927778922955366047639 2232077891668384433049071459)
                ·
                  refine ⟨3348116837502576649573607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232077891668384433049071459 3348116837502576649573607189)
                  ·
                    refine ⟨156942976757933280448762837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3348116837502576649573607189 156942976757933280448762837)
                    ·
                      refine ⟨3678351017764061260517879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156942976757933280448762837 3678351017764061260517879)
                      ·
                        rfl

theorem cell23_7163563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_7163563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163563 prefixEnd_7163563 := by exact prefixLift 7163563
  have htrace : WordTrace (prefixWord ++ tailWord_7163563) baseStart_7163563 baseEnd_7163563 := by
    simpa [prefixWord, tailWord_7163563, baseEnd_7163563] using wordTrace_append hprefix tailTrace_7163563
  have hstable : (prefixWord ++ tailWord_7163563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163563).length < 2 ^ (prefixWord ++ tailWord_7163563).sum := by decide
  have hdescent : baseEnd_7163563 < baseStart_7163563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163607 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_7163607 : Nat := 118140960795 + 7163607 * 2 ^ 59
def prefixEnd_7163607 : Nat := 4983230072969 + 3 ^ 40 * 7163607 * 2
def baseEnd_7163607 : Nat := 3678373610912859088367677

theorem tailTrace_7163607 : CollatzResearch.WordTrace tailWord_7163607 prefixEnd_7163607 3678373610912859088367677 := by
  unfold tailWord_7163607
  simp only [CollatzResearch.WordTrace]
  refine ⟨261278212158482760517145075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174185474772321840344763383 261278212158482760517145075)
  ·
    refine ⟨391917318237724140775717613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261278212158482760517145075 391917318237724140775717613)
    ·
      refine ⟨146968994339146552790894105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391917318237724140775717613 146968994339146552790894105)
      ·
        refine ⟨110226745754359914593170579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146968994339146552790894105 110226745754359914593170579)
        ·
          refine ⟨165340118631539871889755869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110226745754359914593170579 165340118631539871889755869)
          ·
            refine ⟨62002544486827451958658451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165340118631539871889755869 62002544486827451958658451)
            ·
              refine ⟨93003816730241177937987677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62002544486827451958658451 93003816730241177937987677)
              ·
                refine ⟨34876431273840441726745379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93003816730241177937987677 34876431273840441726745379)
                ·
                  refine ⟨52314646910760662590118069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34876431273840441726745379 52314646910760662590118069)
                  ·
                    refine ⟨4904498147883812117823569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52314646910760662590118069 4904498147883812117823569)
                    ·
                      refine ⟨3678373610912859088367677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904498147883812117823569 3678373610912859088367677)
                      ·
                        rfl

theorem cell23_7163607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_7163607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163607 prefixEnd_7163607 := by exact prefixLift 7163607
  have htrace : WordTrace (prefixWord ++ tailWord_7163607) baseStart_7163607 baseEnd_7163607 := by
    simpa [prefixWord, tailWord_7163607, baseEnd_7163607] using wordTrace_append hprefix tailTrace_7163607
  have hstable : (prefixWord ++ tailWord_7163607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163607).length < 2 ^ (prefixWord ++ tailWord_7163607).sum := by decide
  have hdescent : baseEnd_7163607 < baseStart_7163607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163624 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7163624 : Nat := 118140960795 + 7163624 * 2 ^ 59
def prefixEnd_7163624 : Nat := 4983230072969 + 3 ^ 40 * 7163624 * 2
def baseEnd_7163624 : Nat := 3678382340083985521855099

theorem tailTrace_7163624 : CollatzResearch.WordTrace tailWord_7163624 prefixEnd_7163624 3678382340083985521855099 := by
  unfold tailWord_7163624
  simp only [CollatzResearch.WordTrace]
  refine ⟨130639416099710586210256963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174185888132947448280342617 130639416099710586210256963)
  ·
    refine ⟨195959124149565879315385445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130639416099710586210256963 195959124149565879315385445)
    ·
      refine ⟨36742335778043602371634771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195959124149565879315385445 36742335778043602371634771)
      ·
        refine ⟨55113503667065403557452157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36742335778043602371634771 55113503667065403557452157)
        ·
          refine ⟨20667563875149526334044559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55113503667065403557452157 20667563875149526334044559)
          ·
            refine ⟨31001345812724289501066839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20667563875149526334044559 31001345812724289501066839)
            ·
              refine ⟨46502018719086434251600259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31001345812724289501066839 46502018719086434251600259)
              ·
                refine ⟨69753028078629651377400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46502018719086434251600259 69753028078629651377400389)
                ·
                  refine ⟨13078692764743059633262573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69753028078629651377400389 13078692764743059633262573)
                  ·
                    refine ⟨4904509786778647362473465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13078692764743059633262573 4904509786778647362473465)
                    ·
                      refine ⟨3678382340083985521855099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904509786778647362473465 3678382340083985521855099)
                      ·
                        rfl

theorem cell23_7163624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7163624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163624 prefixEnd_7163624 := by exact prefixLift 7163624
  have htrace : WordTrace (prefixWord ++ tailWord_7163624) baseStart_7163624 baseEnd_7163624 := by
    simpa [prefixWord, tailWord_7163624, baseEnd_7163624] using wordTrace_append hprefix tailTrace_7163624
  have hstable : (prefixWord ++ tailWord_7163624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163624).length < 2 ^ (prefixWord ++ tailWord_7163624).sum := by decide
  have hdescent : baseEnd_7163624 < baseStart_7163624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163640 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_7163640 : Nat := 118140960795 + 7163640 * 2 ^ 59
def prefixEnd_7163640 : Nat := 4983230072969 + 3 ^ 40 * 7163640 * 2
def baseEnd_7163640 : Nat := 3678390555774457459255025

theorem tailTrace_7163640 : CollatzResearch.WordTrace tailWord_7163640 prefixEnd_7163640 3678390555774457459255025 := by
  unfold tailWord_7163640
  simp only [CollatzResearch.WordTrace]
  refine ⟨130639707883681603576548187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174186277178242138102064249 130639707883681603576548187)
  ·
    refine ⟨195959561825522405364822281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130639707883681603576548187 195959561825522405364822281)
    ·
      refine ⟨146969671369141804023616711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195959561825522405364822281 146969671369141804023616711)
      ·
        refine ⟨220454507053712706035425067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146969671369141804023616711 220454507053712706035425067)
        ·
          refine ⟨330681760580569059053137601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220454507053712706035425067 330681760580569059053137601)
          ·
            refine ⟨248011320435426794289853201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330681760580569059053137601 248011320435426794289853201)
            ·
              refine ⟨186008490326570095717389901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248011320435426794289853201 186008490326570095717389901)
              ·
                refine ⟨69753183872463785894021213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186008490326570095717389901 69753183872463785894021213)
                ·
                  refine ⟨26157443952173919710257955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69753183872463785894021213 26157443952173919710257955)
                  ·
                    refine ⟨39236165928260879565386933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26157443952173919710257955 39236165928260879565386933)
                    ·
                      refine ⟨3678390555774457459255025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39236165928260879565386933 3678390555774457459255025)
                      ·
                        rfl

theorem cell23_7163640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_7163640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163640 prefixEnd_7163640 := by exact prefixLift 7163640
  have htrace : WordTrace (prefixWord ++ tailWord_7163640) baseStart_7163640 baseEnd_7163640 := by
    simpa [prefixWord, tailWord_7163640, baseEnd_7163640] using wordTrace_append hprefix tailTrace_7163640
  have hstable : (prefixWord ++ tailWord_7163640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163640).length < 2 ^ (prefixWord ++ tailWord_7163640).sum := by decide
  have hdescent : baseEnd_7163640 < baseStart_7163640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163660 : List Nat := [2, 2, 1, 2, 2, 1, 4, 9]
def baseStart_7163660 : Nat := 118140960795 + 7163660 * 2 ^ 59
def prefixEnd_7163660 : Nat := 4983230072969 + 3 ^ 40 * 7163660 * 2
def baseEnd_7163660 : Nat := 136237067606946199296479

theorem tailTrace_7163660 : CollatzResearch.WordTrace tailWord_7163660 prefixEnd_7163660 136237067606946199296479 := by
  unfold tailWord_7163660
  simp only [CollatzResearch.WordTrace]
  refine ⟨130640072613645375284412217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174186763484860500379216289 130640072613645375284412217)
  ·
    refine ⟨97980054460234031463309163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130640072613645375284412217 97980054460234031463309163)
    ·
      refine ⟨146970081690351047194963745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97980054460234031463309163 146970081690351047194963745)
      ·
        refine ⟨110227561267763285396222809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146970081690351047194963745 110227561267763285396222809)
        ·
          refine ⟨82670670950822464047167107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110227561267763285396222809 82670670950822464047167107)
          ·
            refine ⟨124006006426233696070750661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82670670950822464047167107 124006006426233696070750661)
            ·
              refine ⟨23251126204918818013265749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124006006426233696070750661 23251126204918818013265749)
              ·
                refine ⟨136237067606946199296479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23251126204918818013265749 136237067606946199296479)
                ·
                  rfl

theorem cell23_7163660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 9].length) (baseStart_7163660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163660 prefixEnd_7163660 := by exact prefixLift 7163660
  have htrace : WordTrace (prefixWord ++ tailWord_7163660) baseStart_7163660 baseEnd_7163660 := by
    simpa [prefixWord, tailWord_7163660, baseEnd_7163660] using wordTrace_append hprefix tailTrace_7163660
  have hstable : (prefixWord ++ tailWord_7163660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163660).length < 2 ^ (prefixWord ++ tailWord_7163660).sum := by decide
  have hdescent : baseEnd_7163660 < baseStart_7163660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163671 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7163671 : Nat := 118140960795 + 7163671 * 2 ^ 59
def prefixEnd_7163671 : Nat := 4983230072969 + 3 ^ 40 * 7163671 * 2
def baseEnd_7163671 : Nat := 3678406473674746837967383

theorem tailTrace_7163671 : CollatzResearch.WordTrace tailWord_7163671 prefixEnd_7163671 3678406473674746837967383 := by
  unfold tailWord_7163671
  simp only [CollatzResearch.WordTrace]
  refine ⟨261280546430250899447474867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174187030953500599631649911 261280546430250899447474867)
  ·
    refine ⟨391920819645376349171212301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261280546430250899447474867 391920819645376349171212301)
    ·
      refine ⟨146970307367016130939204613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391920819645376349171212301 146970307367016130939204613)
      ·
        refine ⟨27556932631315524551100865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146970307367016130939204613 27556932631315524551100865)
        ·
          refine ⟨20667699473486643413325649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27556932631315524551100865 20667699473486643413325649)
          ·
            refine ⟨15500774605114982559994237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20667699473486643413325649 15500774605114982559994237)
            ·
              refine ⟨5812790476918118459997839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15500774605114982559994237 5812790476918118459997839)
              ·
                refine ⟨8719185715377177689996759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812790476918118459997839 8719185715377177689996759)
                ·
                  refine ⟨13078778573065766534995139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719185715377177689996759 13078778573065766534995139)
                  ·
                    refine ⟨19618167859598649802492709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13078778573065766534995139 19618167859598649802492709)
                    ·
                      refine ⟨3678406473674746837967383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19618167859598649802492709 3678406473674746837967383)
                      ·
                        rfl

theorem cell23_7163671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7163671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163671 prefixEnd_7163671 := by exact prefixLift 7163671
  have htrace : WordTrace (prefixWord ++ tailWord_7163671) baseStart_7163671 baseEnd_7163671 := by
    simpa [prefixWord, tailWord_7163671, baseEnd_7163671] using wordTrace_append hprefix tailTrace_7163671
  have hstable : (prefixWord ++ tailWord_7163671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163671).length < 2 ^ (prefixWord ++ tailWord_7163671).sum := by decide
  have hdescent : baseEnd_7163671 < baseStart_7163671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163674 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_7163674 : Nat := 118140960795 + 7163674 * 2 ^ 59
def prefixEnd_7163674 : Nat := 4983230072969 + 3 ^ 40 * 7163674 * 2
def baseEnd_7163674 : Nat := 3678408014116710326229869

theorem tailTrace_7163674 : CollatzResearch.WordTrace tailWord_7163674 prefixEnd_7163674 3678408014116710326229869 := by
  unfold tailWord_7163674
  simp only [CollatzResearch.WordTrace]
  refine ⟨65320163962310007739958519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174187103899493353973222717 65320163962310007739958519)
  ·
    refine ⟨97980245943465011609937779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65320163962310007739958519 97980245943465011609937779)
    ·
      refine ⟨146970368915197517414906669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97980245943465011609937779 146970368915197517414906669)
      ·
        refine ⟨55113888343199069030590001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146970368915197517414906669 55113888343199069030590001)
        ·
          refine ⟨41335416257399301772942501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55113888343199069030590001 41335416257399301772942501)
          ·
            refine ⟨7750390548262369082426719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41335416257399301772942501 7750390548262369082426719)
            ·
              refine ⟨11625585822393553623640079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750390548262369082426719 11625585822393553623640079)
              ·
                refine ⟨17438378733590330435460119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625585822393553623640079 17438378733590330435460119)
                ·
                  refine ⟨26157568100385495653190179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17438378733590330435460119 26157568100385495653190179)
                  ·
                    refine ⟨39236352150578243479785269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26157568100385495653190179 39236352150578243479785269)
                    ·
                      refine ⟨3678408014116710326229869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39236352150578243479785269 3678408014116710326229869)
                      ·
                        rfl

theorem cell23_7163674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_7163674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163674 prefixEnd_7163674 := by exact prefixLift 7163674
  have htrace : WordTrace (prefixWord ++ tailWord_7163674) baseStart_7163674 baseEnd_7163674 := by
    simpa [prefixWord, tailWord_7163674, baseEnd_7163674] using wordTrace_append hprefix tailTrace_7163674
  have hstable : (prefixWord ++ tailWord_7163674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163674).length < 2 ^ (prefixWord ++ tailWord_7163674).sum := by decide
  have hdescent : baseEnd_7163674 < baseStart_7163674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163704 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_7163704 : Nat := 118140960795 + 7163704 * 2 ^ 59
def prefixEnd_7163704 : Nat := 4983230072969 + 3 ^ 40 * 7163704 * 2
def baseEnd_7163704 : Nat := 3678423418536345208854731

theorem tailTrace_7163704 : CollatzResearch.WordTrace tailWord_7163704 prefixEnd_7163704 3678423418536345208854731 := by
  unfold tailWord_7163704
  simp only [CollatzResearch.WordTrace]
  refine ⟨130640875019565673041713083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174187833359420897388950777 130640875019565673041713083)
  ·
    refine ⟨195961312529348509562569625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130640875019565673041713083 195961312529348509562569625)
    ·
      refine ⟨146970984397011382171927219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195961312529348509562569625 146970984397011382171927219)
      ·
        refine ⟨220456476595517073257890829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146970984397011382171927219 220456476595517073257890829)
        ·
          refine ⟨82671178723318902471709061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220456476595517073257890829 82671178723318902471709061)
          ·
            refine ⟨15500846010622294213445449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82671178723318902471709061 15500846010622294213445449)
            ·
              refine ⟨11625634507966720660084087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15500846010622294213445449 11625634507966720660084087)
              ·
                refine ⟨17438451761950080990126131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625634507966720660084087 17438451761950080990126131)
                ·
                  refine ⟨26157677642925121485189197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17438451761950080990126131 26157677642925121485189197)
                  ·
                    refine ⟨9809129116096920556945949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26157677642925121485189197 9809129116096920556945949)
                    ·
                      refine ⟨3678423418536345208854731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809129116096920556945949 3678423418536345208854731)
                      ·
                        rfl

theorem cell23_7163704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_7163704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163704 prefixEnd_7163704 := by exact prefixLift 7163704
  have htrace : WordTrace (prefixWord ++ tailWord_7163704) baseStart_7163704 baseEnd_7163704 := by
    simpa [prefixWord, tailWord_7163704, baseEnd_7163704] using wordTrace_append hprefix tailTrace_7163704
  have hstable : (prefixWord ++ tailWord_7163704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163704).length < 2 ^ (prefixWord ++ tailWord_7163704).sum := by decide
  have hdescent : baseEnd_7163704 < baseStart_7163704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163725 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7163725 : Nat := 118140960795 + 7163725 * 2 ^ 59
def prefixEnd_7163725 : Nat := 4983230072969 + 3 ^ 40 * 7163725 * 2
def baseEnd_7163725 : Nat := 3678434201630089626692135

theorem tailTrace_7163725 : CollatzResearch.WordTrace tailWord_7163725 prefixEnd_7163725 3678434201630089626692135 := by
  unfold tailWord_7163725
  simp only [CollatzResearch.WordTrace]
  refine ⟨261282515972055266669940629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174188343981370177779960419 261282515972055266669940629)
  ·
    refine ⟨12247617936190090625153467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261282515972055266669940629 12247617936190090625153467)
    ·
      refine ⟨18371426904285135937730201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247617936190090625153467 18371426904285135937730201)
      ·
        refine ⟨13778570178213851953297651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18371426904285135937730201 13778570178213851953297651)
        ·
          refine ⟨20667855267320777929946477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13778570178213851953297651 20667855267320777929946477)
          ·
            refine ⟨7750445725245291723729929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20667855267320777929946477 7750445725245291723729929)
            ·
              refine ⟨5812834293933968792797447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750445725245291723729929 5812834293933968792797447)
              ·
                refine ⟨8719251440900953189196171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812834293933968792797447 8719251440900953189196171)
                ·
                  refine ⟨13078877161351429783794257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719251440900953189196171 13078877161351429783794257)
                  ·
                    refine ⟨9809157871013572337845693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13078877161351429783794257 9809157871013572337845693)
                    ·
                      refine ⟨3678434201630089626692135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809157871013572337845693 3678434201630089626692135)
                      ·
                        rfl

theorem cell23_7163725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7163725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163725 prefixEnd_7163725 := by exact prefixLift 7163725
  have htrace : WordTrace (prefixWord ++ tailWord_7163725) baseStart_7163725 baseEnd_7163725 := by
    simpa [prefixWord, tailWord_7163725, baseEnd_7163725] using wordTrace_append hprefix tailTrace_7163725
  have hstable : (prefixWord ++ tailWord_7163725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163725).length < 2 ^ (prefixWord ++ tailWord_7163725).sum := by decide
  have hdescent : baseEnd_7163725 < baseStart_7163725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163817 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_7163817 : Nat := 118140960795 + 7163817 * 2 ^ 59
def prefixEnd_7163817 : Nat := 4983230072969 + 3 ^ 40 * 7163817 * 2
def baseEnd_7163817 : Nat := 3678481441850303266741711

theorem tailTrace_7163817 : CollatzResearch.WordTrace tailWord_7163817 prefixEnd_7163817 3678481441850303266741711 := by
  unfold tailWord_7163817
  simp only [CollatzResearch.WordTrace]
  refine ⟨261285871487721966382289705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174190580991814644254859803 261285871487721966382289705)
  ·
    refine ⟨195964403615791474786717279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261285871487721966382289705 195964403615791474786717279)
    ·
      refine ⟨293946605423687212180075919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195964403615791474786717279 293946605423687212180075919)
      ·
        refine ⟨440919908135530818270113879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293946605423687212180075919 440919908135530818270113879)
        ·
          refine ⟨661379862203296227405170819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440919908135530818270113879 661379862203296227405170819)
          ·
            refine ⟨992069793304944341107756229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661379862203296227405170819 992069793304944341107756229)
            ·
              refine ⟨186013086244677063957704293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 992069793304944341107756229 186013086244677063957704293)
              ·
                refine ⟨34877453670876949492069555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186013086244677063957704293 34877453670876949492069555)
                ·
                  refine ⟨52316180506315424238104333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34877453670876949492069555 52316180506315424238104333)
                  ·
                    refine ⟨19618567689868284089289125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52316180506315424238104333 19618567689868284089289125)
                    ·
                      refine ⟨3678481441850303266741711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19618567689868284089289125 3678481441850303266741711)
                      ·
                        rfl

theorem cell23_7163817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_7163817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163817 prefixEnd_7163817 := by exact prefixLift 7163817
  have htrace : WordTrace (prefixWord ++ tailWord_7163817) baseStart_7163817 baseEnd_7163817 := by
    simpa [prefixWord, tailWord_7163817, baseEnd_7163817] using wordTrace_append hprefix tailTrace_7163817
  have hstable : (prefixWord ++ tailWord_7163817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163817).length < 2 ^ (prefixWord ++ tailWord_7163817).sum := by decide
  have hdescent : baseEnd_7163817 < baseStart_7163817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163834 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_7163834 : Nat := 118140960795 + 7163834 * 2 ^ 59
def prefixEnd_7163834 : Nat := 4983230072969 + 3 ^ 40 * 7163834 * 2
def baseEnd_7163834 : Nat := 3678490171021429700229133

theorem tailTrace_7163834 : CollatzResearch.WordTrace tailWord_7163834 prefixEnd_7163834 3678490171021429700229133 := by
  unfold tailWord_7163834
  simp only [CollatzResearch.WordTrace]
  refine ⟨65321622882165094571414639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174190994352440252190439037 65321622882165094571414639)
  ·
    refine ⟨97982434323247641857121959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65321622882165094571414639 97982434323247641857121959)
    ·
      refine ⟨146973651484871462785682939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97982434323247641857121959 146973651484871462785682939)
      ·
        refine ⟨220460477227307194178524409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146973651484871462785682939 220460477227307194178524409)
        ·
          refine ⟨165345357920480395633893307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220460477227307194178524409 165345357920480395633893307)
          ·
            refine ⟨248018036880720593450839961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165345357920480395633893307 248018036880720593450839961)
            ·
              refine ⟨186013527660540445088129971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248018036880720593450839961 186013527660540445088129971)
              ·
                refine ⟨279020291490810667632194957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186013527660540445088129971 279020291490810667632194957)
                ·
                  refine ⟨104632609309054000362073109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279020291490810667632194957 104632609309054000362073109)
                  ·
                    refine ⟨4904653561361906266972177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104632609309054000362073109 4904653561361906266972177)
                    ·
                      refine ⟨3678490171021429700229133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904653561361906266972177 3678490171021429700229133)
                      ·
                        rfl

theorem cell23_7163834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_7163834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163834 prefixEnd_7163834 := by exact prefixLift 7163834
  have htrace : WordTrace (prefixWord ++ tailWord_7163834) baseStart_7163834 baseEnd_7163834 := by
    simpa [prefixWord, tailWord_7163834, baseEnd_7163834] using wordTrace_append hprefix tailTrace_7163834
  have hstable : (prefixWord ++ tailWord_7163834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163834).length < 2 ^ (prefixWord ++ tailWord_7163834).sum := by decide
  have hdescent : baseEnd_7163834 < baseStart_7163834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163847 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_7163847 : Nat := 118140960795 + 7163847 * 2 ^ 59
def prefixEnd_7163847 : Nat := 4983230072969 + 3 ^ 40 * 7163847 * 2
def baseEnd_7163847 : Nat := 3678496846269938149366573

theorem tailTrace_7163847 : CollatzResearch.WordTrace tailWord_7163847 prefixEnd_7163847 3678496846269938149366573 := by
  unfold tailWord_7163847
  simp only [CollatzResearch.WordTrace]
  refine ⟨261286965677613281505881795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174191310451742187670587863 261286965677613281505881795)
  ·
    refine ⟨391930448516419922258822693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261286965677613281505881795 391930448516419922258822693)
    ·
      refine ⟨73486959096828735423529255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391930448516419922258822693 73486959096828735423529255)
      ·
        refine ⟨110230438645243103135293883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73486959096828735423529255 110230438645243103135293883)
        ·
          refine ⟨165345657967864654702940825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110230438645243103135293883 165345657967864654702940825)
          ·
            refine ⟨124009243475898491027205619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165345657967864654702940825 124009243475898491027205619)
            ·
              refine ⟨186013865213847736540808429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124009243475898491027205619 186013865213847736540808429)
              ·
                refine ⟨69755199455192901202803161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186013865213847736540808429 69755199455192901202803161)
                ·
                  refine ⟨52316399591394675902102371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69755199455192901202803161 52316399591394675902102371)
                  ·
                    refine ⟨78474599387092013853153557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52316399591394675902102371 78474599387092013853153557)
                    ·
                      refine ⟨3678496846269938149366573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78474599387092013853153557 3678496846269938149366573)
                      ·
                        rfl

theorem cell23_7163847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_7163847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163847 prefixEnd_7163847 := by exact prefixLift 7163847
  have htrace : WordTrace (prefixWord ++ tailWord_7163847) baseStart_7163847 baseEnd_7163847 := by
    simpa [prefixWord, tailWord_7163847, baseEnd_7163847] using wordTrace_append hprefix tailTrace_7163847
  have hstable : (prefixWord ++ tailWord_7163847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163847).length < 2 ^ (prefixWord ++ tailWord_7163847).sum := by decide
  have hdescent : baseEnd_7163847 < baseStart_7163847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163885 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7163885 : Nat := 118140960795 + 7163885 * 2 ^ 59
def prefixEnd_7163885 : Nat := 4983230072969 + 3 ^ 40 * 7163885 * 2
def baseEnd_7163885 : Nat := 3678516358534809000691399

theorem tailTrace_7163885 : CollatzResearch.WordTrace tailWord_7163885 prefixEnd_7163885 3678516358534809000691399 := by
  unfold tailWord_7163885
  simp only [CollatzResearch.WordTrace]
  refine ⟨261288351651475613995765109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174192234434317075997176739 261288351651475613995765109)
  ·
    refine ⟨24495782967325838812102979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261288351651475613995765109 24495782967325838812102979)
    ·
      refine ⟨36743674450988758218154469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24495782967325838812102979 36743674450988758218154469)
      ·
        refine ⟨6889438959560392165903963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36743674450988758218154469 6889438959560392165903963)
        ·
          refine ⟨10334158439340588248855945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6889438959560392165903963 10334158439340588248855945)
          ·
            refine ⟨7750618829505441186641959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10334158439340588248855945 7750618829505441186641959)
            ·
              refine ⟨11625928244258161779962939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750618829505441186641959 11625928244258161779962939)
              ·
                refine ⟨17438892366387242669944409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625928244258161779962939 17438892366387242669944409)
                ·
                  refine ⟨13079169274790432002458307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17438892366387242669944409 13079169274790432002458307)
                  ·
                    refine ⟨19618753912185648003687461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13079169274790432002458307 19618753912185648003687461)
                    ·
                      refine ⟨3678516358534809000691399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19618753912185648003687461 3678516358534809000691399)
                      ·
                        rfl

theorem cell23_7163885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7163885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163885 prefixEnd_7163885 := by exact prefixLift 7163885
  have htrace : WordTrace (prefixWord ++ tailWord_7163885) baseStart_7163885 baseEnd_7163885 := by
    simpa [prefixWord, tailWord_7163885, baseEnd_7163885] using wordTrace_append hprefix tailTrace_7163885
  have hstable : (prefixWord ++ tailWord_7163885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163885).length < 2 ^ (prefixWord ++ tailWord_7163885).sum := by decide
  have hdescent : baseEnd_7163885 < baseStart_7163885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163918 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7163918 : Nat := 118140960795 + 7163918 * 2 ^ 59
def prefixEnd_7163918 : Nat := 4983230072969 + 3 ^ 40 * 7163918 * 2
def baseEnd_7163918 : Nat := 3678533303396407371578747

theorem tailTrace_7163918 : CollatzResearch.WordTrace tailWord_7163918 prefixEnd_7163918 3678533303396407371578747 := by
  unfold tailWord_7163918
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661194407544507578964551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174193036840237373754477605 32661194407544507578964551)
  ·
    refine ⟨48991791611316761368446827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32661194407544507578964551 48991791611316761368446827)
    ·
      refine ⟨73487687416975142052670241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48991791611316761368446827 73487687416975142052670241)
      ·
        refine ⟨55115765562731356539502681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73487687416975142052670241 55115765562731356539502681)
        ·
          refine ⟨41336824172048517404627011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55115765562731356539502681 41336824172048517404627011)
          ·
            refine ⟨62005236258072776106940517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41336824172048517404627011 62005236258072776106940517)
            ·
              refine ⟨11625981798388645520051347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62005236258072776106940517 11625981798388645520051347)
              ·
                refine ⟨17438972697582968280077021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625981798388645520051347 17438972697582968280077021)
                ·
                  refine ⟨6539614761593613105028883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17438972697582968280077021 6539614761593613105028883)
                  ·
                    refine ⟨9809422142390419657543325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539614761593613105028883 9809422142390419657543325)
                    ·
                      refine ⟨3678533303396407371578747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809422142390419657543325 3678533303396407371578747)
                      ·
                        rfl

theorem cell23_7163918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7163918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163918 prefixEnd_7163918 := by exact prefixLift 7163918
  have htrace : WordTrace (prefixWord ++ tailWord_7163918) baseStart_7163918 baseEnd_7163918 := by
    simpa [prefixWord, tailWord_7163918, baseEnd_7163918] using wordTrace_append hprefix tailTrace_7163918
  have hstable : (prefixWord ++ tailWord_7163918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163918).length < 2 ^ (prefixWord ++ tailWord_7163918).sum := by decide
  have hdescent : baseEnd_7163918 < baseStart_7163918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163941 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_7163941 : Nat := 118140960795 + 7163941 * 2 ^ 59
def prefixEnd_7163941 : Nat := 4983230072969 + 3 ^ 40 * 7163941 * 2
def baseEnd_7163941 : Nat := 3678545113451460781591141

theorem tailTrace_7163941 : CollatzResearch.WordTrace tailWord_7163941 prefixEnd_7163941 3678545113451460781591141 := by
  unfold tailWord_7163941
  simp only [CollatzResearch.WordTrace]
  refine ⟨261290394139272735559803677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174193596092848490373202451 261290394139272735559803677)
  ·
    refine ⟨97983897802227275834926379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261290394139272735559803677 97983897802227275834926379)
    ·
      refine ⟨146975846703340913752389569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97983897802227275834926379 146975846703340913752389569)
      ·
        refine ⟨110231885027505685314292177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146975846703340913752389569 110231885027505685314292177)
        ·
          refine ⟨82673913770629263985719133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110231885027505685314292177 82673913770629263985719133)
          ·
            refine ⟨31002717663985973994644675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82673913770629263985719133 31002717663985973994644675)
            ·
              refine ⟨46504076495978960991967013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31002717663985973994644675 46504076495978960991967013)
              ·
                refine ⟨8719514342996055185993815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46504076495978960991967013 8719514342996055185993815)
                ·
                  refine ⟨13079271514494082778990723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719514342996055185993815 13079271514494082778990723)
                  ·
                    refine ⟨19618907271741124168486085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13079271514494082778990723 19618907271741124168486085)
                    ·
                      refine ⟨3678545113451460781591141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19618907271741124168486085 3678545113451460781591141)
                      ·
                        rfl

theorem cell23_7163941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_7163941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163941 prefixEnd_7163941 := by exact prefixLift 7163941
  have htrace : WordTrace (prefixWord ++ tailWord_7163941) baseStart_7163941 baseEnd_7163941 := by
    simpa [prefixWord, tailWord_7163941, baseEnd_7163941] using wordTrace_append hprefix tailTrace_7163941
  have hstable : (prefixWord ++ tailWord_7163941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163941).length < 2 ^ (prefixWord ++ tailWord_7163941).sum := by decide
  have hdescent : baseEnd_7163941 < baseStart_7163941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163958 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7163958 : Nat := 118140960795 + 7163958 * 2 ^ 59
def prefixEnd_7163958 : Nat := 4983230072969 + 3 ^ 40 * 7163958 * 2
def baseEnd_7163958 : Nat := 3678553842622587215078563

theorem tailTrace_7163958 : CollatzResearch.WordTrace tailWord_7163958 prefixEnd_7163958 3678553842622587215078563 := by
  unfold tailWord_7163958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330688386263196716448283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174194009453474098308781685 16330688386263196716448283)
  ·
    refine ⟨24496032579394795074672425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16330688386263196716448283 24496032579394795074672425)
    ·
      refine ⟨18372024434546096306004319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24496032579394795074672425 18372024434546096306004319)
      ·
        refine ⟨27558036651819144459006479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18372024434546096306004319 27558036651819144459006479)
        ·
          refine ⟨41337054977728716688509719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27558036651819144459006479 41337054977728716688509719)
          ·
            refine ⟨62005582466593075032764579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41337054977728716688509719 62005582466593075032764579)
            ·
              refine ⟨93008373699889612549146869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62005582466593075032764579 93008373699889612549146869)
              ·
                refine ⟨8719535034364651176482519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93008373699889612549146869 8719535034364651176482519)
                ·
                  refine ⟨13079302551546976764723779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8719535034364651176482519 13079302551546976764723779)
                  ·
                    refine ⟨19618953827320465147085669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13079302551546976764723779 19618953827320465147085669)
                    ·
                      refine ⟨3678553842622587215078563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19618953827320465147085669 3678553842622587215078563)
                      ·
                        rfl

theorem cell23_7163958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7163958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163958 prefixEnd_7163958 := by exact prefixLift 7163958
  have htrace : WordTrace (prefixWord ++ tailWord_7163958) baseStart_7163958 baseEnd_7163958 := by
    simpa [prefixWord, tailWord_7163958, baseEnd_7163958] using wordTrace_append hprefix tailTrace_7163958
  have hstable : (prefixWord ++ tailWord_7163958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163958).length < 2 ^ (prefixWord ++ tailWord_7163958).sum := by decide
  have hdescent : baseEnd_7163958 < baseStart_7163958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7163981 : List Nat := [1, 6, 1, 1, 1, 1, 4, 8]
def baseStart_7163981 : Nat := 118140960795 + 7163981 * 2 ^ 59
def prefixEnd_7163981 : Nat := 4983230072969 + 3 ^ 40 * 7163981 * 2
def baseEnd_7163981 : Nat := 136243172321394097225591

theorem tailTrace_7163981 : CollatzResearch.WordTrace tailWord_7163981 prefixEnd_7163981 136243172321394097225591 := by
  unfold tailWord_7163981
  simp only [CollatzResearch.WordTrace]
  refine ⟨261291853059127822391259797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174194568706085214927506531 261291853059127822391259797)
  ·
    refine ⟨12248055612146616674590303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261291853059127822391259797 12248055612146616674590303)
    ·
      refine ⟨18372083418219925011885455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12248055612146616674590303 18372083418219925011885455)
      ·
        refine ⟨27558125127329887517828183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18372083418219925011885455 27558125127329887517828183)
        ·
          refine ⟨41337187690994831276742275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27558125127329887517828183 41337187690994831276742275)
          ·
            refine ⟨62005781536492246915113413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41337187690994831276742275 62005781536492246915113413)
            ·
              refine ⟨11626084038092296296583765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62005781536492246915113413 11626084038092296296583765)
              ·
                refine ⟨136243172321394097225591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11626084038092296296583765 136243172321394097225591)
                ·
                  rfl

theorem cell23_7163981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 8].length) (baseStart_7163981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7163981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7163981 prefixEnd_7163981 := by exact prefixLift 7163981
  have htrace : WordTrace (prefixWord ++ tailWord_7163981) baseStart_7163981 baseEnd_7163981 := by
    simpa [prefixWord, tailWord_7163981, baseEnd_7163981] using wordTrace_append hprefix tailTrace_7163981
  have hstable : (prefixWord ++ tailWord_7163981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7163981).length < 2 ^ (prefixWord ++ tailWord_7163981).sum := by decide
  have hdescent : baseEnd_7163981 < baseStart_7163981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7163981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164004 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_7164004 : Nat := 118140960795 + 7164004 * 2 ^ 59
def prefixEnd_7164004 : Nat := 4983230072969 + 3 ^ 40 * 7164004 * 2
def baseEnd_7164004 : Nat := 3678577462732694035103351

theorem tailTrace_7164004 : CollatzResearch.WordTrace tailWord_7164004 prefixEnd_7164004 3678577462732694035103351 := by
  unfold tailWord_7164004
  simp only [CollatzResearch.WordTrace]
  refine ⟨130646345969022248659673533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174195127958696331546231377 130646345969022248659673533)
  ·
    refine ⟨48992379738383343247377575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130646345969022248659673533 48992379738383343247377575)
    ·
      refine ⟨73488569607575014871066363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48992379738383343247377575 73488569607575014871066363)
      ·
        refine ⟨110232854411362522306599545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73488569607575014871066363 110232854411362522306599545)
        ·
          refine ⟨82674640808521891729949659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110232854411362522306599545 82674640808521891729949659)
          ·
            refine ⟨124011961212782837594924489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82674640808521891729949659 124011961212782837594924489)
            ·
              refine ⟨93008970909587128196193367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124011961212782837594924489 93008970909587128196193367)
              ·
                refine ⟨139513456364380692294290051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93008970909587128196193367 139513456364380692294290051)
                ·
                  refine ⟨209270184546571038441435077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139513456364380692294290051 209270184546571038441435077)
                  ·
                    refine ⟨39238159602482069707769077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209270184546571038441435077 39238159602482069707769077)
                    ·
                      refine ⟨3678577462732694035103351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39238159602482069707769077 3678577462732694035103351)
                      ·
                        rfl

theorem cell23_7164004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_7164004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164004 prefixEnd_7164004 := by exact prefixLift 7164004
  have htrace : WordTrace (prefixWord ++ tailWord_7164004) baseStart_7164004 baseEnd_7164004 := by
    simpa [prefixWord, tailWord_7164004, baseEnd_7164004] using wordTrace_append hprefix tailTrace_7164004
  have hstable : (prefixWord ++ tailWord_7164004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164004).length < 2 ^ (prefixWord ++ tailWord_7164004).sum := by decide
  have hdescent : baseEnd_7164004 < baseStart_7164004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164024 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_7164024 : Nat := 118140960795 + 7164024 * 2 ^ 59
def prefixEnd_7164024 : Nat := 4983230072969 + 3 ^ 40 * 7164024 * 2
def baseEnd_7164024 : Nat := 1226195910781927985617753

theorem tailTrace_7164024 : CollatzResearch.WordTrace tailWord_7164024 prefixEnd_7164024 1226195910781927985617753 := by
  unfold tailWord_7164024
  simp only [CollatzResearch.WordTrace]
  refine ⟨130646710698986020367537563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174195614265314693823383417 130646710698986020367537563)
  ·
    refine ⟨195970066048479030551306345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130646710698986020367537563 195970066048479030551306345)
    ·
      refine ⟨146977549536359272913479759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195970066048479030551306345 146977549536359272913479759)
      ·
        refine ⟨220466324304538909370219639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146977549536359272913479759 220466324304538909370219639)
        ·
          refine ⟨330699486456808364055329459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220466324304538909370219639 330699486456808364055329459)
          ·
            refine ⟨496049229685212546082994189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330699486456808364055329459 496049229685212546082994189)
            ·
              refine ⟨186018461131954704781122821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496049229685212546082994189 186018461131954704781122821)
              ·
                refine ⟨34878461462241507146460529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186018461131954704781122821 34878461462241507146460529)
                ·
                  refine ⟨26158846096681130359845397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34878461462241507146460529 26158846096681130359845397)
                  ·
                    refine ⟨1226195910781927985617753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26158846096681130359845397 1226195910781927985617753)
                    ·
                      rfl

theorem cell23_7164024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_7164024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164024 prefixEnd_7164024 := by exact prefixLift 7164024
  have htrace : WordTrace (prefixWord ++ tailWord_7164024) baseStart_7164024 baseEnd_7164024 := by
    simpa [prefixWord, tailWord_7164024, baseEnd_7164024] using wordTrace_append hprefix tailTrace_7164024
  have hstable : (prefixWord ++ tailWord_7164024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164024).length < 2 ^ (prefixWord ++ tailWord_7164024).sum := by decide
  have hdescent : baseEnd_7164024 < baseStart_7164024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164025 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_7164025 : Nat := 118140960795 + 7164025 * 2 ^ 59
def prefixEnd_7164025 : Nat := 4983230072969 + 3 ^ 40 * 7164025 * 2
def baseEnd_7164025 : Nat := 3678588245826438452940755

theorem tailTrace_7164025 : CollatzResearch.WordTrace tailWord_7164025 prefixEnd_7164025 3678588245826438452940755 := by
  unfold tailWord_7164025
  simp only [CollatzResearch.WordTrace]
  refine ⟨261293457870968417905861529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174195638580645611937241019 261293457870968417905861529)
  ·
    refine ⟨195970093403226313429396147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261293457870968417905861529 195970093403226313429396147)
    ·
      refine ⟨293955140104839470144094221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195970093403226313429396147 293955140104839470144094221)
      ·
        refine ⟨110233177539314801304035333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293955140104839470144094221 110233177539314801304035333)
        ·
          refine ⟨20668720788621525244506625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110233177539314801304035333 20668720788621525244506625)
          ·
            refine ⟨15501540591466143933379969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20668720788621525244506625 15501540591466143933379969)
            ·
              refine ⟨11626155443599607950034977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15501540591466143933379969 11626155443599607950034977)
              ·
                refine ⟨8719616582699705962526233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11626155443599607950034977 8719616582699705962526233)
                ·
                  refine ⟨6539712437024779471894675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719616582699705962526233 6539712437024779471894675)
                  ·
                    refine ⟨9809568655537169207842013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539712437024779471894675 9809568655537169207842013)
                    ·
                      refine ⟨3678588245826438452940755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809568655537169207842013 3678588245826438452940755)
                      ·
                        rfl

theorem cell23_7164025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_7164025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164025 prefixEnd_7164025 := by exact prefixLift 7164025
  have htrace : WordTrace (prefixWord ++ tailWord_7164025) baseStart_7164025 baseEnd_7164025 := by
    simpa [prefixWord, tailWord_7164025, baseEnd_7164025] using wordTrace_append hprefix tailTrace_7164025
  have hstable : (prefixWord ++ tailWord_7164025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164025).length < 2 ^ (prefixWord ++ tailWord_7164025).sum := by decide
  have hdescent : baseEnd_7164025 < baseStart_7164025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164048 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2]
def baseStart_7164048 : Nat := 118140960795 + 7164048 * 2 ^ 59
def prefixEnd_7164048 : Nat := 4983230072969 + 3 ^ 40 * 7164048 * 2
def baseEnd_7164048 : Nat := 3678600055881491862953149

theorem tailTrace_7164048 : CollatzResearch.WordTrace tailWord_7164048 prefixEnd_7164048 3678600055881491862953149 := by
  unfold tailWord_7164048
  simp only [CollatzResearch.WordTrace]
  refine ⟨130647148374942546416974399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174196197833256728555965865 130647148374942546416974399)
  ·
    refine ⟨195970722562413819625461599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130647148374942546416974399 195970722562413819625461599)
    ·
      refine ⟨293956083843620729438192399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195970722562413819625461599 293956083843620729438192399)
      ·
        refine ⟨440934125765431094157288599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293956083843620729438192399 440934125765431094157288599)
        ·
          refine ⟨661401188648146641235932899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440934125765431094157288599 661401188648146641235932899)
          ·
            refine ⟨992101782972219961853899349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661401188648146641235932899 992101782972219961853899349)
            ·
              refine ⟨11626192769205702677975383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 992101782972219961853899349 11626192769205702677975383)
              ·
                refine ⟨17439289153808554016963075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626192769205702677975383 17439289153808554016963075)
                ·
                  refine ⟨26158933730712831025444613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17439289153808554016963075 26158933730712831025444613)
                  ·
                    refine ⟨4904800074508655817270865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26158933730712831025444613 4904800074508655817270865)
                    ·
                      refine ⟨3678600055881491862953149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904800074508655817270865 3678600055881491862953149)
                      ·
                        rfl

theorem cell23_7164048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2].length) (baseStart_7164048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164048 prefixEnd_7164048 := by exact prefixLift 7164048
  have htrace : WordTrace (prefixWord ++ tailWord_7164048) baseStart_7164048 baseEnd_7164048 := by
    simpa [prefixWord, tailWord_7164048, baseEnd_7164048] using wordTrace_append hprefix tailTrace_7164048
  have hstable : (prefixWord ++ tailWord_7164048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164048).length < 2 ^ (prefixWord ++ tailWord_7164048).sum := by decide
  have hdescent : baseEnd_7164048 < baseStart_7164048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164121 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_7164121 : Nat := 118140960795 + 7164121 * 2 ^ 59
def prefixEnd_7164121 : Nat := 4983230072969 + 3 ^ 40 * 7164121 * 2
def baseEnd_7164121 : Nat := 3678637539969270077340313

theorem tailTrace_7164121 : CollatzResearch.WordTrace tailWord_7164121 prefixEnd_7164121 3678637539969270077340313 := by
  unfold tailWord_7164121
  simp only [CollatzResearch.WordTrace]
  refine ⟨261296959278620626301356217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174197972852413750867570811 261296959278620626301356217)
  ·
    refine ⟨195972719458965469726017163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261296959278620626301356217 195972719458965469726017163)
    ·
      refine ⟨293959079188448204589025745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195972719458965469726017163 293959079188448204589025745)
      ·
        refine ⟨220469309391336153441769309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293959079188448204589025745 220469309391336153441769309)
        ·
          refine ⟨82675991021751057540663491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220469309391336153441769309 82675991021751057540663491)
          ·
            refine ⟨124013986532626586310995237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82675991021751057540663491 124013986532626586310995237)
            ·
              refine ⟨23252622474867484933311607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124013986532626586310995237 23252622474867484933311607)
              ·
                refine ⟨34878933712301227399967411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23252622474867484933311607 34878933712301227399967411)
                ·
                  refine ⟨52318400568451841099951117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34878933712301227399967411 52318400568451841099951117)
                  ·
                    refine ⟨19619400213169440412481669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52318400568451841099951117 19619400213169440412481669)
                    ·
                      refine ⟨3678637539969270077340313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19619400213169440412481669 3678637539969270077340313)
                      ·
                        rfl

theorem cell23_7164121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_7164121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164121 prefixEnd_7164121 := by exact prefixLift 7164121
  have htrace : WordTrace (prefixWord ++ tailWord_7164121) baseStart_7164121 baseEnd_7164121 := by
    simpa [prefixWord, tailWord_7164121, baseEnd_7164121] using wordTrace_append hprefix tailTrace_7164121
  have hstable : (prefixWord ++ tailWord_7164121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164121).length < 2 ^ (prefixWord ++ tailWord_7164121).sum := by decide
  have hdescent : baseEnd_7164121 < baseStart_7164121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164138 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7164138 : Nat := 118140960795 + 7164138 * 2 ^ 59
def prefixEnd_7164138 : Nat := 4983230072969 + 3 ^ 40 * 7164138 * 2
def baseEnd_7164138 : Nat := 3678646269140396510827735

theorem tailTrace_7164138 : CollatzResearch.WordTrace tailWord_7164138 prefixEnd_7164138 3678646269140396510827735 := by
  unfold tailWord_7164138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65324394829889759551181267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174198386213039358803150045 65324394829889759551181267)
  ·
    refine ⟨97986592244834639326771901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65324394829889759551181267 97986592244834639326771901)
    ·
      refine ⟨36744972091812989747539463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97986592244834639326771901 36744972091812989747539463)
      ·
        refine ⟨55117458137719484621309195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36744972091812989747539463 55117458137719484621309195)
        ·
          refine ⟨82676187206579226931963793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55117458137719484621309195 82676187206579226931963793)
          ·
            refine ⟨62007140404934420198972845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82676187206579226931963793 62007140404934420198972845)
            ·
              refine ⟨23252677651850407574614817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62007140404934420198972845 23252677651850407574614817)
              ·
                refine ⟨17439508238887805680961113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23252677651850407574614817 17439508238887805680961113)
                ·
                  refine ⟨13079631179165854260720835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17439508238887805680961113 13079631179165854260720835)
                  ·
                    refine ⟨19619446768748781391081253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13079631179165854260720835 19619446768748781391081253)
                    ·
                      refine ⟨3678646269140396510827735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19619446768748781391081253 3678646269140396510827735)
                      ·
                        rfl

theorem cell23_7164138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7164138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164138 prefixEnd_7164138 := by exact prefixLift 7164138
  have htrace : WordTrace (prefixWord ++ tailWord_7164138) baseStart_7164138 baseEnd_7164138 := by
    simpa [prefixWord, tailWord_7164138, baseEnd_7164138] using wordTrace_append hprefix tailTrace_7164138
  have hstable : (prefixWord ++ tailWord_7164138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164138).length < 2 ^ (prefixWord ++ tailWord_7164138).sum := by decide
  have hdescent : baseEnd_7164138 < baseStart_7164138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164222 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7164222 : Nat := 118140960795 + 7164222 * 2 ^ 59
def prefixEnd_7164222 : Nat := 4983230072969 + 3 ^ 40 * 7164222 * 2
def baseEnd_7164222 : Nat := 3678689401515374182177349

theorem tailTrace_7164222 : CollatzResearch.WordTrace tailWord_7164222 prefixEnd_7164222 3678689401515374182177349 := by
  unfold tailWord_7164222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662580381406840068847865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174200428700836480367188613 32662580381406840068847865)
  ·
    refine ⟨24496935286055130051635899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32662580381406840068847865 24496935286055130051635899)
    ·
      refine ⟨36745402929082695077453849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24496935286055130051635899 36745402929082695077453849)
      ·
        refine ⟨27559052196812021308090387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36745402929082695077453849 27559052196812021308090387)
        ·
          refine ⟨41338578295218031962135581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559052196812021308090387 41338578295218031962135581)
          ·
            refine ⟨15501966860706761985800843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41338578295218031962135581 15501966860706761985800843)
            ·
              refine ⟨23252950291060142978701265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15501966860706761985800843 23252950291060142978701265)
              ·
                refine ⟨17439712718295107234025949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23252950291060142978701265 17439712718295107234025949)
                ·
                  refine ⟨6539892269360665212759731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17439712718295107234025949 6539892269360665212759731)
                  ·
                    refine ⟨9809838404040997819139597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539892269360665212759731 9809838404040997819139597)
                    ·
                      refine ⟨3678689401515374182177349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809838404040997819139597 3678689401515374182177349)
                      ·
                        rfl

theorem cell23_7164222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7164222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164222 prefixEnd_7164222 := by exact prefixLift 7164222
  have htrace : WordTrace (prefixWord ++ tailWord_7164222) baseStart_7164222 baseEnd_7164222 := by
    simpa [prefixWord, tailWord_7164222, baseEnd_7164222] using wordTrace_append hprefix tailTrace_7164222
  have hstable : (prefixWord ++ tailWord_7164222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164222).length < 2 ^ (prefixWord ++ tailWord_7164222).sum := by decide
  have hdescent : baseEnd_7164222 < baseStart_7164222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164248 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7164248 : Nat := 118140960795 + 7164248 * 2 ^ 59
def prefixEnd_7164248 : Nat := 4983230072969 + 3 ^ 40 * 7164248 * 2
def baseEnd_7164248 : Nat := 3678702752012391080452229

theorem tailTrace_7164248 : CollatzResearch.WordTrace tailWord_7164248 prefixEnd_7164248 3678702752012391080452229 := by
  unfold tailWord_7164248
  simp only [CollatzResearch.WordTrace]
  refine ⟨130650795674580263495614699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174201060899440351327486265 130650795674580263495614699)
  ·
    refine ⟨195976193511870395243422049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130650795674580263495614699 195976193511870395243422049)
    ·
      refine ⟨146982145133902796432566537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195976193511870395243422049 146982145133902796432566537)
      ·
        refine ⟨110236608850427097324424903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146982145133902796432566537 110236608850427097324424903)
        ·
          refine ⟨165354913275640645986637355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110236608850427097324424903 165354913275640645986637355)
          ·
            refine ⟨248032369913460968979956033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165354913275640645986637355 248032369913460968979956033)
            ·
              refine ⟨186024277435095726734967025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248032369913460968979956033 186024277435095726734967025)
              ·
                refine ⟨139518208076321795051225269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186024277435095726734967025 139518208076321795051225269)
                ·
                  refine ⟨13079832007155168286052369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139518208076321795051225269 13079832007155168286052369)
                  ·
                    refine ⟨9809874005366376214539277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13079832007155168286052369 9809874005366376214539277)
                    ·
                      refine ⟨3678702752012391080452229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809874005366376214539277 3678702752012391080452229)
                      ·
                        rfl

theorem cell23_7164248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7164248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164248 prefixEnd_7164248 := by exact prefixLift 7164248
  have htrace : WordTrace (prefixWord ++ tailWord_7164248) baseStart_7164248 baseEnd_7164248 := by
    simpa [prefixWord, tailWord_7164248, baseEnd_7164248] using wordTrace_append hprefix tailTrace_7164248
  have hstable : (prefixWord ++ tailWord_7164248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164248).length < 2 ^ (prefixWord ++ tailWord_7164248).sum := by decide
  have hdescent : baseEnd_7164248 < baseStart_7164248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164255 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 2, 4]
def baseStart_7164255 : Nat := 118140960795 + 7164255 * 2 ^ 59
def prefixEnd_7164255 : Nat := 4983230072969 + 3 ^ 40 * 7164255 * 2
def baseEnd_7164255 : Nat := 1226235448792324184354899

theorem tailTrace_7164255 : CollatzResearch.WordTrace tailWord_7164255 prefixEnd_7164255 1226235448792324184354899 := by
  unfold tailWord_7164255
  simp only [CollatzResearch.WordTrace]
  refine ⟨261301846660135167186734219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174201231106756778124489479 261301846660135167186734219)
  ·
    refine ⟨391952769990202750780101329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261301846660135167186734219 391952769990202750780101329)
    ·
      refine ⟨293964577492652063085075997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391952769990202750780101329 293964577492652063085075997)
      ·
        refine ⟨110236716559744523656903499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293964577492652063085075997 110236716559744523656903499)
        ·
          refine ⟨165355074839616785485355249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110236716559744523656903499 165355074839616785485355249)
          ·
            refine ⟨124016306129712589114016437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165355074839616785485355249 124016306129712589114016437)
            ·
              refine ⟨11626528699660555229439041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124016306129712589114016437 11626528699660555229439041)
              ·
                refine ⟨8719896524745416422079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11626528699660555229439041 8719896524745416422079281)
                ·
                  refine ⟨6539922393559062316559461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719896524745416422079281 6539922393559062316559461)
                  ·
                    refine ⟨1226235448792324184354899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539922393559062316559461 1226235448792324184354899)
                    ·
                      rfl

theorem cell23_7164255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_7164255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164255 prefixEnd_7164255 := by exact prefixLift 7164255
  have htrace : WordTrace (prefixWord ++ tailWord_7164255) baseStart_7164255 baseEnd_7164255 := by
    simpa [prefixWord, tailWord_7164255, baseEnd_7164255] using wordTrace_append hprefix tailTrace_7164255
  have hstable : (prefixWord ++ tailWord_7164255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164255).length < 2 ^ (prefixWord ++ tailWord_7164255).sum := by decide
  have hdescent : baseEnd_7164255 < baseStart_7164255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_7164271 : Nat := 118140960795 + 7164271 * 2 ^ 59
def prefixEnd_7164271 : Nat := 4983230072969 + 3 ^ 40 * 7164271 * 2
def baseEnd_7164271 : Nat := 3678714562067444490464623

theorem tailTrace_7164271 : CollatzResearch.WordTrace tailWord_7164271 prefixEnd_7164271 3678714562067444490464623 := by
  unfold tailWord_7164271
  simp only [CollatzResearch.WordTrace]
  refine ⟨261302430228077201919316667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174201620152051467946211111 261302430228077201919316667)
  ·
    refine ⟨391953645342115802878975001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261302430228077201919316667 391953645342115802878975001)
    ·
      refine ⟨293965234006586852159231251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391953645342115802878975001 293965234006586852159231251)
      ·
        refine ⟨440947851009880278238846877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293965234006586852159231251 440947851009880278238846877)
        ·
          refine ⟨165355444128705104339567579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440947851009880278238846877 165355444128705104339567579)
          ·
            refine ⟨248033166193057656509351369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165355444128705104339567579 248033166193057656509351369)
            ·
              refine ⟨186024874644793242382013527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248033166193057656509351369 186024874644793242382013527)
              ·
                refine ⟨279037311967189863573020291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186024874644793242382013527 279037311967189863573020291)
                ·
                  refine ⟨418555967950784795359530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279037311967189863573020291 418555967950784795359530437)
                  ·
                    refine ⟨78479243990772149129911957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418555967950784795359530437 78479243990772149129911957)
                    ·
                      refine ⟨3678714562067444490464623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78479243990772149129911957 3678714562067444490464623)
                      ·
                        rfl

theorem cell23_7164271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_7164271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164271 prefixEnd_7164271 := by exact prefixLift 7164271
  have htrace : WordTrace (prefixWord ++ tailWord_7164271) baseStart_7164271 baseEnd_7164271 := by
    simpa [prefixWord, tailWord_7164271, baseEnd_7164271] using wordTrace_append hprefix tailTrace_7164271
  have hstable : (prefixWord ++ tailWord_7164271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164271).length < 2 ^ (prefixWord ++ tailWord_7164271).sum := by decide
  have hdescent : baseEnd_7164271 < baseStart_7164271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164272 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_7164272 : Nat := 118140960795 + 7164272 * 2 ^ 59
def prefixEnd_7164272 : Nat := 4983230072969 + 3 ^ 40 * 7164272 * 2
def baseEnd_7164272 : Nat := 1226238358516032995517373

theorem tailTrace_7164272 : CollatzResearch.WordTrace tailWord_7164272 prefixEnd_7164272 1226238358516032995517373 := by
  unfold tailWord_7164272
  simp only [CollatzResearch.WordTrace]
  refine ⟨130651233350536789545051535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174201644467382386060068713 130651233350536789545051535)
  ·
    refine ⟨195976850025805184317577303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130651233350536789545051535 195976850025805184317577303)
    ·
      refine ⟨293965275038707776476365955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195976850025805184317577303 293965275038707776476365955)
      ·
        refine ⟨440947912558061664714548933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293965275038707776476365955 440947912558061664714548933)
        ·
          refine ⟨82677733604636562133977925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440947912558061664714548933 82677733604636562133977925)
          ·
            refine ⟨15502075050869355400120861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82677733604636562133977925 15502075050869355400120861)
            ·
              refine ⟨5813278144076008275045323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15502075050869355400120861 5813278144076008275045323)
              ·
                refine ⟨8719917216114012412567985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813278144076008275045323 8719917216114012412567985)
                ·
                  refine ⟨6539937912085509309425989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719917216114012412567985 6539937912085509309425989)
                  ·
                    refine ⟨1226238358516032995517373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539937912085509309425989 1226238358516032995517373)
                    ·
                      rfl

theorem cell23_7164272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_7164272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164272 prefixEnd_7164272 := by exact prefixLift 7164272
  have htrace : WordTrace (prefixWord ++ tailWord_7164272) baseStart_7164272 baseEnd_7164272 := by
    simpa [prefixWord, tailWord_7164272, baseEnd_7164272] using wordTrace_append hprefix tailTrace_7164272
  have hstable : (prefixWord ++ tailWord_7164272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164272).length < 2 ^ (prefixWord ++ tailWord_7164272).sum := by decide
  have hdescent : baseEnd_7164272 < baseStart_7164272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164285 : List Nat := [1, 4, 1, 1, 2, 5, 2, 7]
def baseStart_7164285 : Nat := 118140960795 + 7164285 * 2 ^ 59
def prefixEnd_7164285 : Nat := 4983230072969 + 3 ^ 40 * 7164285 * 2
def baseEnd_7164285 : Nat := 136248953733207682803317

theorem tailTrace_7164285 : CollatzResearch.WordTrace tailWord_7164285 prefixEnd_7164285 136248953733207682803317 := by
  unfold tailWord_7164285
  simp only [CollatzResearch.WordTrace]
  refine ⟨261302940850026482310326309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174201960566684321540217539 261302940850026482310326309)
  ·
    refine ⟨48994301409379965433186183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261302940850026482310326309 48994301409379965433186183)
    ·
      refine ⟨73491452114069948149779275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994301409379965433186183 73491452114069948149779275)
      ·
        refine ⟨110237178171104922224668913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73491452114069948149779275 110237178171104922224668913)
        ·
          refine ⟨82677883628328691668501685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110237178171104922224668913 82677883628328691668501685)
          ·
            refine ⟨7751051590155814843922033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82677883628328691668501685 7751051590155814843922033)
            ·
              refine ⟨5813288692616861132941525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751051590155814843922033 5813288692616861132941525)
              ·
                refine ⟨136248953733207682803317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5813288692616861132941525 136248953733207682803317)
                ·
                  rfl

theorem cell23_7164285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 7].length) (baseStart_7164285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164285 prefixEnd_7164285 := by exact prefixLift 7164285
  have htrace : WordTrace (prefixWord ++ tailWord_7164285) baseStart_7164285 baseEnd_7164285 := by
    simpa [prefixWord, tailWord_7164285, baseEnd_7164285] using wordTrace_append hprefix tailTrace_7164285
  have hstable : (prefixWord ++ tailWord_7164285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164285).length < 2 ^ (prefixWord ++ tailWord_7164285).sum := by decide
  have hdescent : baseEnd_7164285 < baseStart_7164285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164290 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7164290 : Nat := 118140960795 + 7164290 * 2 ^ 59
def prefixEnd_7164290 : Nat := 4983230072969 + 3 ^ 40 * 7164290 * 2
def baseEnd_7164290 : Nat := 3678724318199879916127037

theorem tailTrace_7164290 : CollatzResearch.WordTrace tailWord_7164290 prefixEnd_7164290 3678724318199879916127037 := by
  unfold tailWord_7164290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65325780803752092041064581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174202082143338912109505549 65325780803752092041064581)
  ·
    refine ⟨12248583900703517257699609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65325780803752092041064581 12248583900703517257699609)
    ·
      refine ⟨9186437925527637943274707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12248583900703517257699609 9186437925527637943274707)
      ·
        refine ⟨13779656888291456914912061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186437925527637943274707 13779656888291456914912061)
        ·
          refine ⟨5167371333109296343092023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13779656888291456914912061 5167371333109296343092023)
          ·
            refine ⟨7751056999663944514638035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167371333109296343092023 7751056999663944514638035)
            ·
              refine ⟨11626585499495916771957053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751056999663944514638035 11626585499495916771957053)
              ·
                refine ⟨4359969562310968789483895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11626585499495916771957053 4359969562310968789483895)
                ·
                  refine ⟨6539954343466453184225843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359969562310968789483895 6539954343466453184225843)
                  ·
                    refine ⟨9809931515199679776338765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539954343466453184225843 9809931515199679776338765)
                    ·
                      refine ⟨3678724318199879916127037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809931515199679776338765 3678724318199879916127037)
                      ·
                        rfl

theorem cell23_7164290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7164290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164290 prefixEnd_7164290 := by exact prefixLift 7164290
  have htrace : WordTrace (prefixWord ++ tailWord_7164290) baseStart_7164290 baseEnd_7164290 := by
    simpa [prefixWord, tailWord_7164290, baseEnd_7164290] using wordTrace_append hprefix tailTrace_7164290
  have hstable : (prefixWord ++ tailWord_7164290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164290).length < 2 ^ (prefixWord ++ tailWord_7164290).sum := by decide
  have hdescent : baseEnd_7164290 < baseStart_7164290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164295 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_7164295 : Nat := 118140960795 + 7164295 * 2 ^ 59
def prefixEnd_7164295 : Nat := 4983230072969 + 3 ^ 40 * 7164295 * 2
def baseEnd_7164295 : Nat := 3678726885603152396564513

theorem tailTrace_7164295 : CollatzResearch.WordTrace tailWord_7164295 prefixEnd_7164295 3678726885603152396564513 := by
  unfold tailWord_7164295
  simp only [CollatzResearch.WordTrace]
  refine ⟨261303305579990254018190339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174202203719993502678793559 261303305579990254018190339)
  ·
    refine ⟨391954958369985381027285509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261303305579990254018190339 391954958369985381027285509)
    ·
      refine ⟨73491554694372258942616033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391954958369985381027285509 73491554694372258942616033)
      ·
        refine ⟨55118666020779194206962025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73491554694372258942616033 55118666020779194206962025)
        ·
          refine ⟨41338999515584395655221519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55118666020779194206962025 41338999515584395655221519)
          ·
            refine ⟨62008499273376593482832279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41338999515584395655221519 62008499273376593482832279)
            ·
              refine ⟨93012748910064890224248419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62008499273376593482832279 93012748910064890224248419)
              ·
                refine ⟨139519123365097335336372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93012748910064890224248419 139519123365097335336372629)
                ·
                  refine ⟨6539958907738937593892467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139519123365097335336372629 6539958907738937593892467)
                  ·
                    refine ⟨9809938361608406390838701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539958907738937593892467 9809938361608406390838701)
                    ·
                      refine ⟨3678726885603152396564513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809938361608406390838701 3678726885603152396564513)
                      ·
                        rfl

theorem cell23_7164295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_7164295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164295 prefixEnd_7164295 := by exact prefixLift 7164295
  have htrace : WordTrace (prefixWord ++ tailWord_7164295) baseStart_7164295 baseEnd_7164295 := by
    simpa [prefixWord, tailWord_7164295, baseEnd_7164295] using wordTrace_append hprefix tailTrace_7164295
  have hstable : (prefixWord ++ tailWord_7164295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164295).length < 2 ^ (prefixWord ++ tailWord_7164295).sum := by decide
  have hdescent : baseEnd_7164295 < baseStart_7164295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164312 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7164312 : Nat := 118140960795 + 7164312 * 2 ^ 59
def prefixEnd_7164312 : Nat := 4983230072969 + 3 ^ 40 * 7164312 * 2
def baseEnd_7164312 : Nat := 3678735614774278830051935

theorem tailTrace_7164312 : CollatzResearch.WordTrace tailWord_7164312 prefixEnd_7164312 3678735614774278830051935 := by
  unfold tailWord_7164312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130651962810464332960779595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174202617080619110614372793 130651962810464332960779595)
  ·
    refine ⟨195977944215696499441169393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130651962810464332960779595 195977944215696499441169393)
    ·
      refine ⟨146983458161772374580877045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195977944215696499441169393 146983458161772374580877045)
      ·
        refine ⟨13779699202666160116957223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146983458161772374580877045 13779699202666160116957223)
        ·
          refine ⟨20669548803999240175435835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13779699202666160116957223 20669548803999240175435835)
          ·
            refine ⟨31004323205998860263153753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20669548803999240175435835 31004323205998860263153753)
            ·
              refine ⟨23253242404499145197365315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31004323205998860263153753 23253242404499145197365315)
              ·
                refine ⟨34879863606748717796047973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23253242404499145197365315 34879863606748717796047973)
                ·
                  refine ⟨6539974426265384586758995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34879863606748717796047973 6539974426265384586758995)
                  ·
                    refine ⟨9809961639398076880138493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6539974426265384586758995 9809961639398076880138493)
                    ·
                      refine ⟨3678735614774278830051935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9809961639398076880138493 3678735614774278830051935)
                      ·
                        rfl

theorem cell23_7164312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7164312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164312 prefixEnd_7164312 := by exact prefixLift 7164312
  have htrace : WordTrace (prefixWord ++ tailWord_7164312) baseStart_7164312 baseEnd_7164312 := by
    simpa [prefixWord, tailWord_7164312, baseEnd_7164312] using wordTrace_append hprefix tailTrace_7164312
  have hstable : (prefixWord ++ tailWord_7164312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164312).length < 2 ^ (prefixWord ++ tailWord_7164312).sum := by decide
  have hdescent : baseEnd_7164312 < baseStart_7164312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164322 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_7164322 : Nat := 118140960795 + 7164322 * 2 ^ 59
def prefixEnd_7164322 : Nat := 4983230072969 + 3 ^ 40 * 7164322 * 2
def baseEnd_7164322 : Nat := 3678740749580823790926889

theorem tailTrace_7164322 : CollatzResearch.WordTrace tailWord_7164322 prefixEnd_7164322 3678740749580823790926889 := by
  unfold tailWord_7164322
  simp only [CollatzResearch.WordTrace]
  refine ⟨65326072587723109407355805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174202860233928291752948813 65326072587723109407355805)
  ·
    refine ⟨24497277220396166027758427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65326072587723109407355805 24497277220396166027758427)
    ·
      refine ⟨36745915830594249041637641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24497277220396166027758427 36745915830594249041637641)
      ·
        refine ⟨27559436872945686781228231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36745915830594249041637641 27559436872945686781228231)
        ·
          refine ⟨41339155309418530171842347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559436872945686781228231 41339155309418530171842347)
          ·
            refine ⟨62008732964127795257763521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41339155309418530171842347 62008732964127795257763521)
            ·
              refine ⟨46506549723095846443322641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62008732964127795257763521 46506549723095846443322641)
              ·
                refine ⟨34879912292321884832491981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46506549723095846443322641 34879912292321884832491981)
                ·
                  refine ⟨13079967109620706812184493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34879912292321884832491981 13079967109620706812184493)
                  ·
                    refine ⟨4904987666107765054569185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13079967109620706812184493 4904987666107765054569185)
                    ·
                      refine ⟨3678740749580823790926889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4904987666107765054569185 3678740749580823790926889)
                      ·
                        rfl

theorem cell23_7164322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_7164322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164322 prefixEnd_7164322 := by exact prefixLift 7164322
  have htrace : WordTrace (prefixWord ++ tailWord_7164322) baseStart_7164322 baseEnd_7164322 := by
    simpa [prefixWord, tailWord_7164322, baseEnd_7164322] using wordTrace_append hprefix tailTrace_7164322
  have hstable : (prefixWord ++ tailWord_7164322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164322).length < 2 ^ (prefixWord ++ tailWord_7164322).sum := by decide
  have hdescent : baseEnd_7164322 < baseStart_7164322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164338 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7164338 : Nat := 118140960795 + 7164338 * 2 ^ 59
def prefixEnd_7164338 : Nat := 4983230072969 + 3 ^ 40 * 7164338 * 2
def baseEnd_7164338 : Nat := 3678748965271295728326815

theorem tailTrace_7164338 : CollatzResearch.WordTrace tailWord_7164338 prefixEnd_7164338 3678748965271295728326815 := by
  unfold tailWord_7164338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65326218479708618090501417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174203249279222981574670445 65326218479708618090501417)
  ·
    refine ⟨48994663859781463567876063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65326218479708618090501417 48994663859781463567876063)
    ·
      refine ⟨73491995789672195351814095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994663859781463567876063 73491995789672195351814095)
      ·
        refine ⟨110237993684508293027721143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73491995789672195351814095 110237993684508293027721143)
        ·
          refine ⟨165356990526762439541581715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110237993684508293027721143 165356990526762439541581715)
          ·
            refine ⟨248035485790143659312372573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165356990526762439541581715 248035485790143659312372573)
            ·
              refine ⟨93013307171303872242139715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248035485790143659312372573 93013307171303872242139715)
              ·
                refine ⟨139519960756955808363209573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93013307171303872242139715 139519960756955808363209573)
                ·
                  refine ⟨26159992641929214068101795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139519960756955808363209573 26159992641929214068101795)
                  ·
                    refine ⟨39239988962893821102152693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26159992641929214068101795 39239988962893821102152693)
                    ·
                      refine ⟨3678748965271295728326815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39239988962893821102152693 3678748965271295728326815)
                      ·
                        rfl

theorem cell23_7164338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7164338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164338 prefixEnd_7164338 := by exact prefixLift 7164338
  have htrace : WordTrace (prefixWord ++ tailWord_7164338) baseStart_7164338 baseEnd_7164338 := by
    simpa [prefixWord, tailWord_7164338, baseEnd_7164338] using wordTrace_append hprefix tailTrace_7164338
  have hstable : (prefixWord ++ tailWord_7164338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164338).length < 2 ^ (prefixWord ++ tailWord_7164338).sum := by decide
  have hdescent : baseEnd_7164338 < baseStart_7164338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164385 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_7164385 : Nat := 118140960795 + 7164385 * 2 ^ 59
def prefixEnd_7164385 : Nat := 4983230072969 + 3 ^ 40 * 7164385 * 2
def baseEnd_7164385 : Nat := 3678773098862057044439099

theorem tailTrace_7164385 : CollatzResearch.WordTrace tailWord_7164385 prefixEnd_7164385 3678773098862057044439099 := by
  unfold tailWord_7164385
  simp only [CollatzResearch.WordTrace]
  refine ⟨261306588149664199388966609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174204392099776132925977739 261306588149664199388966609)
  ·
    refine ⟨195979941112248149541724957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261306588149664199388966609 195979941112248149541724957)
    ·
      refine ⟨73492477917093056078146859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195979941112248149541724957 73492477917093056078146859)
      ·
        refine ⟨110238716875639584117220289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73492477917093056078146859 110238716875639584117220289)
        ·
          refine ⟨82679037656729688087915217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110238716875639584117220289 82679037656729688087915217)
          ·
            refine ⟨62009278242547266065936413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82679037656729688087915217 62009278242547266065936413)
            ·
              refine ⟨23253479340955224774726155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62009278242547266065936413 23253479340955224774726155)
              ·
                refine ⟨34880219011432837162089233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23253479340955224774726155 34880219011432837162089233)
                ·
                  refine ⟨26160164258574627871566925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34880219011432837162089233 26160164258574627871566925)
                  ·
                    refine ⟨9810061596965485451837597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26160164258574627871566925 9810061596965485451837597)
                    ·
                      refine ⟨3678773098862057044439099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9810061596965485451837597 3678773098862057044439099)
                      ·
                        rfl

theorem cell23_7164385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_7164385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164385 prefixEnd_7164385 := by exact prefixLift 7164385
  have htrace : WordTrace (prefixWord ++ tailWord_7164385) baseStart_7164385 baseEnd_7164385 := by
    simpa [prefixWord, tailWord_7164385, baseEnd_7164385] using wordTrace_append hprefix tailTrace_7164385
  have hstable : (prefixWord ++ tailWord_7164385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164385).length < 2 ^ (prefixWord ++ tailWord_7164385).sum := by decide
  have hdescent : baseEnd_7164385 < baseStart_7164385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164395 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 5, 2]
def baseStart_7164395 : Nat := 118140960795 + 7164395 * 2 ^ 59
def prefixEnd_7164395 : Nat := 4983230072969 + 3 ^ 40 * 7164395 * 2
def baseEnd_7164395 : Nat := 3678778233668602005314053

theorem tailTrace_7164395 : CollatzResearch.WordTrace tailWord_7164395 prefixEnd_7164395 3678778233668602005314053 := by
  unfold tailWord_7164395
  simp only [CollatzResearch.WordTrace]
  refine ⟨261306952879627971096830639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174204635253085314064553759 261306952879627971096830639)
  ·
    refine ⟨391960429319441956645245959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261306952879627971096830639 391960429319441956645245959)
    ·
      refine ⟨587940643979162934967868939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391960429319441956645245959 587940643979162934967868939)
      ·
        refine ⟨881910965968744402451803409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587940643979162934967868939 881910965968744402451803409)
        ·
          refine ⟨661433224476558301838852557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881910965968744402451803409 661433224476558301838852557)
          ·
            refine ⟨248037459178709363189569709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661433224476558301838852557 248037459178709363189569709)
            ·
              refine ⟨93014047192016011196088641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248037459178709363189569709 93014047192016011196088641)
              ·
                refine ⟨69760535394012008397066481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93014047192016011196088641 69760535394012008397066481)
                ·
                  refine ⟨52320401545509006297799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69760535394012008397066481 52320401545509006297799861)
                  ·
                    refine ⟨4905037644891469340418737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52320401545509006297799861 4905037644891469340418737)
                    ·
                      refine ⟨3678778233668602005314053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905037644891469340418737 3678778233668602005314053)
                      ·
                        rfl

theorem cell23_7164395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5, 2].length) (baseStart_7164395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164395 prefixEnd_7164395 := by exact prefixLift 7164395
  have htrace : WordTrace (prefixWord ++ tailWord_7164395) baseStart_7164395 baseEnd_7164395 := by
    simpa [prefixWord, tailWord_7164395, baseEnd_7164395] using wordTrace_append hprefix tailTrace_7164395
  have hstable : (prefixWord ++ tailWord_7164395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164395).length < 2 ^ (prefixWord ++ tailWord_7164395).sum := by decide
  have hdescent : baseEnd_7164395 < baseStart_7164395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164442 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_7164442 : Nat := 118140960795 + 7164442 * 2 ^ 59
def prefixEnd_7164442 : Nat := 4983230072969 + 3 ^ 40 * 7164442 * 2
def baseEnd_7164442 : Nat := 3678802367259363321426337

theorem tailTrace_7164442 : CollatzResearch.WordTrace tailWord_7164442 prefixEnd_7164442 3678802367259363321426337 := by
  unfold tailWord_7164442
  simp only [CollatzResearch.WordTrace]
  refine ⟨65327166777614424530947895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174205778073638465415861053 65327166777614424530947895)
  ·
    refine ⟨97990750166421636796421843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65327166777614424530947895 97990750166421636796421843)
    ·
      refine ⟨146986125249632455194632765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97990750166421636796421843 146986125249632455194632765)
      ·
        refine ⟨55119796968612170697987287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146986125249632455194632765 55119796968612170697987287)
        ·
          refine ⟨82679695452918256046980931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55119796968612170697987287 82679695452918256046980931)
          ·
            refine ⟨124019543179377384070471397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82679695452918256046980931 124019543179377384070471397)
            ·
              refine ⟨23253664346133259513213387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124019543179377384070471397 23253664346133259513213387)
              ·
                refine ⟨34880496519199889269820081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23253664346133259513213387 34880496519199889269820081)
                ·
                  refine ⟨26160372389399916952365061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34880496519199889269820081 26160372389399916952365061)
                  ·
                    refine ⟨4905069823012484428568449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26160372389399916952365061 4905069823012484428568449)
                    ·
                      refine ⟨3678802367259363321426337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905069823012484428568449 3678802367259363321426337)
                      ·
                        rfl

theorem cell23_7164442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_7164442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164442 prefixEnd_7164442 := by exact prefixLift 7164442
  have htrace : WordTrace (prefixWord ++ tailWord_7164442) baseStart_7164442 baseEnd_7164442 := by
    simpa [prefixWord, tailWord_7164442, baseEnd_7164442] using wordTrace_append hprefix tailTrace_7164442
  have hstable : (prefixWord ++ tailWord_7164442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164442).length < 2 ^ (prefixWord ++ tailWord_7164442).sum := by decide
  have hdescent : baseEnd_7164442 < baseStart_7164442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164486 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_7164486 : Nat := 118140960795 + 7164486 * 2 ^ 59
def prefixEnd_7164486 : Nat := 4983230072969 + 3 ^ 40 * 7164486 * 2
def baseEnd_7164486 : Nat := 1226274986802720383092045

theorem tailTrace_7164486 : CollatzResearch.WordTrace tailWord_7164486 prefixEnd_7164486 1226274986802720383092045 := by
  unfold tailWord_7164486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165945997571821676199791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174206847948198862425595541 8165945997571821676199791)
  ·
    refine ⟨12248918996357732514299687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8165945997571821676199791 12248918996357732514299687)
    ·
      refine ⟨18373378494536598771449531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12248918996357732514299687 18373378494536598771449531)
      ·
        refine ⟨27560067741804898157174297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18373378494536598771449531 27560067741804898157174297)
        ·
          refine ⟨20670050806353673617880723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27560067741804898157174297 20670050806353673617880723)
          ·
            refine ⟨31005076209530510426821085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20670050806353673617880723 31005076209530510426821085)
            ·
              refine ⟨11626903578573941410057907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31005076209530510426821085 11626903578573941410057907)
              ·
                refine ⟨17440355367860912115086861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626903578573941410057907 17440355367860912115086861)
                ·
                  refine ⟨6540133262947842043157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17440355367860912115086861 6540133262947842043157573)
                  ·
                    refine ⟨1226274986802720383092045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540133262947842043157573 1226274986802720383092045)
                    ·
                      rfl

theorem cell23_7164486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_7164486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164486 prefixEnd_7164486 := by exact prefixLift 7164486
  have htrace : WordTrace (prefixWord ++ tailWord_7164486) baseStart_7164486 baseEnd_7164486 := by
    simpa [prefixWord, tailWord_7164486, baseEnd_7164486] using wordTrace_append hprefix tailTrace_7164486
  have hstable : (prefixWord ++ tailWord_7164486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164486).length < 2 ^ (prefixWord ++ tailWord_7164486).sum := by decide
  have hdescent : baseEnd_7164486 < baseStart_7164486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164512 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_7164512 : Nat := 118140960795 + 7164512 * 2 ^ 59
def prefixEnd_7164512 : Nat := 4983230072969 + 3 ^ 40 * 7164512 * 2
def baseEnd_7164512 : Nat := 1226279436968392682517005

theorem tailTrace_7164512 : CollatzResearch.WordTrace tailWord_7164512 prefixEnd_7164512 1226279436968392682517005 := by
  unfold tailWord_7164512
  simp only [CollatzResearch.WordTrace]
  refine ⟨130655610110102050039419895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174207480146802733385893193 130655610110102050039419895)
  ·
    refine ⟨195983415165153075059129843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130655610110102050039419895 195983415165153075059129843)
    ·
      refine ⟨293975122747729612588694765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195983415165153075059129843 293975122747729612588694765)
      ·
        refine ⟨110240671030398604720760537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293975122747729612588694765 110240671030398604720760537)
        ·
          refine ⟨82680503272798953540570403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110240671030398604720760537 82680503272798953540570403)
          ·
            refine ⟨124020754909198430310855605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82680503272798953540570403 124020754909198430310855605)
            ·
              refine ⟨11626945772737352841642713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124020754909198430310855605 11626945772737352841642713)
              ·
                refine ⟨8720209329553014631232035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11626945772737352841642713 8720209329553014631232035)
                ·
                  refine ⟨13080313994329521946848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720209329553014631232035 13080313994329521946848053)
                  ·
                    refine ⟨1226279436968392682517005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13080313994329521946848053 1226279436968392682517005)
                    ·
                      rfl

theorem cell23_7164512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_7164512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164512 prefixEnd_7164512 := by exact prefixLift 7164512
  have htrace : WordTrace (prefixWord ++ tailWord_7164512) baseStart_7164512 baseEnd_7164512 := by
    simpa [prefixWord, tailWord_7164512, baseEnd_7164512] using wordTrace_append hprefix tailTrace_7164512
  have hstable : (prefixWord ++ tailWord_7164512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164512).length < 2 ^ (prefixWord ++ tailWord_7164512).sum := by decide
  have hdescent : baseEnd_7164512 < baseStart_7164512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164570 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7164570 : Nat := 118140960795 + 7164570 * 2 ^ 59
def prefixEnd_7164570 : Nat := 4983230072969 + 3 ^ 40 * 7164570 * 2
def baseEnd_7164570 : Nat := 3678868092783138820625749

theorem tailTrace_7164570 : CollatzResearch.WordTrace tailWord_7164570 prefixEnd_7164570 3678868092783138820625749 := by
  unfold tailWord_7164570
  simp only [CollatzResearch.WordTrace]
  refine ⟨65328333913498493996112791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174208890435995983989634109 65328333913498493996112791)
  ·
    refine ⟨97992500870247740994169187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65328333913498493996112791 97992500870247740994169187)
    ·
      refine ⟨146988751305371611491253781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97992500870247740994169187 146988751305371611491253781)
      ·
        refine ⟨6890097717439294288652521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146988751305371611491253781 6890097717439294288652521)
        ·
          refine ⟨5167573288079470716489391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890097717439294288652521 5167573288079470716489391)
          ·
            refine ⟨7751359932119206074734087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167573288079470716489391 7751359932119206074734087)
            ·
              refine ⟨11627039898178809112101131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751359932119206074734087 11627039898178809112101131)
              ·
                refine ⟨17440559847268213668151697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627039898178809112101131 17440559847268213668151697)
                ·
                  refine ⟨13080419885451160251113773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17440559847268213668151697 13080419885451160251113773)
                  ·
                    refine ⟨4905157457044185094167665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13080419885451160251113773 4905157457044185094167665)
                    ·
                      refine ⟨3678868092783138820625749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905157457044185094167665 3678868092783138820625749)
                      ·
                        rfl

theorem cell23_7164570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7164570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164570 prefixEnd_7164570 := by exact prefixLift 7164570
  have htrace : WordTrace (prefixWord ++ tailWord_7164570) baseStart_7164570 baseEnd_7164570 := by
    simpa [prefixWord, tailWord_7164570, baseEnd_7164570] using wordTrace_append hprefix tailTrace_7164570
  have hstable : (prefixWord ++ tailWord_7164570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164570).length < 2 ^ (prefixWord ++ tailWord_7164570).sum := by decide
  have hdescent : baseEnd_7164570 < baseStart_7164570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164593 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_7164593 : Nat := 118140960795 + 7164593 * 2 ^ 59
def prefixEnd_7164593 : Nat := 4983230072969 + 3 ^ 40 * 7164593 * 2
def baseEnd_7164593 : Nat := 1226293300946064076879381

theorem tailTrace_7164593 : CollatzResearch.WordTrace tailWord_7164593 prefixEnd_7164593 1226293300946064076879381 := by
  unfold tailWord_7164593
  simp only [CollatzResearch.WordTrace]
  refine ⟨261314174532910650912538433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174209449688607100608358955 261314174532910650912538433)
  ·
    refine ⟨195985630899682988184403825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261314174532910650912538433 195985630899682988184403825)
    ·
      refine ⟨146989223174762241138302869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195985630899682988184403825 146989223174762241138302869)
      ·
        refine ⟨6890119836316980053357947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146989223174762241138302869 6890119836316980053357947)
        ·
          refine ⟨10335179754475470080036921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890119836316980053357947 10335179754475470080036921)
          ·
            refine ⟨7751384815856602560027691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335179754475470080036921 7751384815856602560027691)
            ·
              refine ⟨11627077223784903840041537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751384815856602560027691 11627077223784903840041537)
              ·
                refine ⟨8720307917838677880031153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11627077223784903840041537 8720307917838677880031153)
                ·
                  refine ⟨6540230938379008410023365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8720307917838677880031153 6540230938379008410023365)
                  ·
                    refine ⟨1226293300946064076879381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540230938379008410023365 1226293300946064076879381)
                    ·
                      rfl

theorem cell23_7164593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_7164593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164593 prefixEnd_7164593 := by exact prefixLift 7164593
  have htrace : WordTrace (prefixWord ++ tailWord_7164593) baseStart_7164593 baseEnd_7164593 := by
    simpa [prefixWord, tailWord_7164593, baseEnd_7164593] using wordTrace_append hprefix tailTrace_7164593
  have hstable : (prefixWord ++ tailWord_7164593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164593).length < 2 ^ (prefixWord ++ tailWord_7164593).sum := by decide
  have hdescent : baseEnd_7164593 < baseStart_7164593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164615 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 8]
def baseStart_7164615 : Nat := 118140960795 + 7164615 * 2 ^ 59
def prefixEnd_7164615 : Nat := 4983230072969 + 3 ^ 40 * 7164615 * 2
def baseEnd_7164615 : Nat := 1226297066470863714854347

theorem tailTrace_7164615 : CollatzResearch.WordTrace tailWord_7164615 prefixEnd_7164615 1226297066470863714854347 := by
  unfold tailWord_7164615
  simp only [CollatzResearch.WordTrace]
  refine ⟨261314976938830948669839299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174209984625887299113226199 261314976938830948669839299)
  ·
    refine ⟨391972465408246423004758949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261314976938830948669839299 391972465408246423004758949)
    ·
      refine ⟨73494837264046204313392303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391972465408246423004758949 73494837264046204313392303)
      ·
        refine ⟨110242255896069306470088455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73494837264046204313392303 110242255896069306470088455)
        ·
          refine ⟨165363383844103959705132683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110242255896069306470088455 165363383844103959705132683)
          ·
            refine ⟨248045075766155939557699025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165363383844103959705132683 248045075766155939557699025)
            ·
              refine ⟨186033806824616954668274269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248045075766155939557699025 186033806824616954668274269)
              ·
                refine ⟨69762677559231358000602851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186033806824616954668274269 69762677559231358000602851)
                ·
                  refine ⟨104644016338847037000904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69762677559231358000602851 104644016338847037000904277)
                  ·
                    refine ⟨1226297066470863714854347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104644016338847037000904277 1226297066470863714854347)
                    ·
                      rfl

theorem cell23_7164615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_7164615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164615 prefixEnd_7164615 := by exact prefixLift 7164615
  have htrace : WordTrace (prefixWord ++ tailWord_7164615) baseStart_7164615 baseEnd_7164615 := by
    simpa [prefixWord, tailWord_7164615, baseEnd_7164615] using wordTrace_append hprefix tailTrace_7164615
  have hstable : (prefixWord ++ tailWord_7164615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164615).length < 2 ^ (prefixWord ++ tailWord_7164615).sum := by decide
  have hdescent : baseEnd_7164615 < baseStart_7164615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164656 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2]
def baseStart_7164656 : Nat := 118140960795 + 7164656 * 2 ^ 59
def prefixEnd_7164656 : Nat := 4983230072969 + 3 ^ 40 * 7164656 * 2
def baseEnd_7164656 : Nat := 3678912252119425484150353

theorem tailTrace_7164656 : CollatzResearch.WordTrace tailWord_7164656 prefixEnd_7164656 3678912252119425484150353 := by
  unfold tailWord_7164656
  simp only [CollatzResearch.WordTrace]
  refine ⟨130658236165841206336040911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174210981554454941781387881 130658236165841206336040911)
  ·
    refine ⟨195987354248761809504061367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130658236165841206336040911 195987354248761809504061367)
    ·
      refine ⟨293981031373142714256092051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195987354248761809504061367 293981031373142714256092051)
      ·
        refine ⟨440971547059714071384138077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293981031373142714256092051 440971547059714071384138077)
        ·
          refine ⟨165364330147392776769051779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440971547059714071384138077 165364330147392776769051779)
          ·
            refine ⟨248046495221089165153577669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165364330147392776769051779 248046495221089165153577669)
            ·
              refine ⟨46508717853954218466295813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248046495221089165153577669 46508717853954218466295813)
              ·
                refine ⟨8720384597616415962430465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46508717853954218466295813 8720384597616415962430465)
                ·
                  refine ⟨6540288448212311971822849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8720384597616415962430465 6540288448212311971822849)
                  ·
                    refine ⟨4905216336159233978867137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540288448212311971822849 4905216336159233978867137)
                    ·
                      refine ⟨3678912252119425484150353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905216336159233978867137 3678912252119425484150353)
                      ·
                        rfl

theorem cell23_7164656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2].length) (baseStart_7164656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164656 prefixEnd_7164656 := by exact prefixLift 7164656
  have htrace : WordTrace (prefixWord ++ tailWord_7164656) baseStart_7164656 baseEnd_7164656 := by
    simpa [prefixWord, tailWord_7164656, baseEnd_7164656] using wordTrace_append hprefix tailTrace_7164656
  have hstable : (prefixWord ++ tailWord_7164656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164656).length < 2 ^ (prefixWord ++ tailWord_7164656).sum := by decide
  have hdescent : baseEnd_7164656 < baseStart_7164656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164739 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 3, 4]
def baseStart_7164739 : Nat := 118140960795 + 7164739 * 2 ^ 59
def prefixEnd_7164739 : Nat := 4983230072969 + 3 ^ 40 * 7164739 * 2
def baseEnd_7164739 : Nat := 1226318290337916219804157

theorem tailTrace_7164739 : CollatzResearch.WordTrace tailWord_7164739 prefixEnd_7164739 1226318290337916219804157 := by
  unfold tailWord_7164739
  simp only [CollatzResearch.WordTrace]
  refine ⟨261319499590381717847353271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174212999726921145231568847 261319499590381717847353271)
  ·
    refine ⟨391979249385572576771029907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261319499590381717847353271 391979249385572576771029907)
    ·
      refine ⟨587968874078358865156544861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391979249385572576771029907 587968874078358865156544861)
      ·
        refine ⟨220488327779384574433704323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587968874078358865156544861 220488327779384574433704323)
        ·
          refine ⟨330732491669076861650556485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220488327779384574433704323 330732491669076861650556485)
          ·
            refine ⟨62012342187951911559479341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330732491669076861650556485 62012342187951911559479341)
            ·
              refine ⟨23254628320481966834804753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62012342187951911559479341 23254628320481966834804753)
              ·
                refine ⟨17440971240361475126103565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23254628320481966834804753 17440971240361475126103565)
                ·
                  refine ⟨6540364215135553172288837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17440971240361475126103565 6540364215135553172288837)
                  ·
                    refine ⟨1226318290337916219804157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540364215135553172288837 1226318290337916219804157)
                    ·
                      rfl

theorem cell23_7164739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 4].length) (baseStart_7164739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164739 prefixEnd_7164739 := by exact prefixLift 7164739
  have htrace : WordTrace (prefixWord ++ tailWord_7164739) baseStart_7164739 baseEnd_7164739 := by
    simpa [prefixWord, tailWord_7164739, baseEnd_7164739] using wordTrace_append hprefix tailTrace_7164739
  have hstable : (prefixWord ++ tailWord_7164739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164739).length < 2 ^ (prefixWord ++ tailWord_7164739).sum := by decide
  have hdescent : baseEnd_7164739 < baseStart_7164739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164799 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 1, 5]
def baseStart_7164799 : Nat := 118140960795 + 7164799 * 2 ^ 59
def prefixEnd_7164799 : Nat := 4983230072969 + 3 ^ 40 * 7164799 * 2
def baseEnd_7164799 : Nat := 1226328559951006141554065

theorem tailTrace_7164799 : CollatzResearch.WordTrace tailWord_7164799 prefixEnd_7164799 1226328559951006141554065 := by
  unfold tailWord_7164799
  simp only [CollatzResearch.WordTrace]
  refine ⟨261321687970164348094537451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174214458646776232063024967 261321687970164348094537451)
  ·
    refine ⟨391982531955246522141806177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261321687970164348094537451 391982531955246522141806177)
    ·
      refine ⟨293986898966434891606354633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391982531955246522141806177 293986898966434891606354633)
      ·
        refine ⟨220490174224826168704765975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293986898966434891606354633 220490174224826168704765975)
        ·
          refine ⟨330735261337239253057148963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220490174224826168704765975 330735261337239253057148963)
          ·
            refine ⟨496102892005858879585723445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330735261337239253057148963 496102892005858879585723445)
            ·
              refine ⟨46509646125549269961161573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 496102892005858879585723445 46509646125549269961161573)
              ·
                refine ⟨8720558648540488117717795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46509646125549269961161573 8720558648540488117717795)
                ·
                  refine ⟨13080837972810732176576693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720558648540488117717795 13080837972810732176576693)
                  ·
                    refine ⟨1226328559951006141554065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13080837972810732176576693 1226328559951006141554065)
                    ·
                      rfl

theorem cell23_7164799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_7164799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164799 prefixEnd_7164799 := by exact prefixLift 7164799
  have htrace : WordTrace (prefixWord ++ tailWord_7164799) baseStart_7164799 baseEnd_7164799 := by
    simpa [prefixWord, tailWord_7164799, baseEnd_7164799] using wordTrace_append hprefix tailTrace_7164799
  have hstable : (prefixWord ++ tailWord_7164799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164799).length < 2 ^ (prefixWord ++ tailWord_7164799).sum := by decide
  have hdescent : baseEnd_7164799 < baseStart_7164799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164853 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_7164853 : Nat := 118140960795 + 7164853 * 2 ^ 59
def prefixEnd_7164853 : Nat := 4983230072969 + 3 ^ 40 * 7164853 * 2
def baseEnd_7164853 : Nat := 3679013407808361213386947

theorem tailTrace_7164853 : CollatzResearch.WordTrace tailWord_7164853 prefixEnd_7164853 3679013407808361213386947 := by
  unfold tailWord_7164853
  simp only [CollatzResearch.WordTrace]
  refine ⟨261323657511968715317003213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174215771674645810211335475 261323657511968715317003213)
  ·
    refine ⟨97996371566988268243876205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261323657511968715317003213 97996371566988268243876205)
    ·
      refine ⟨36748639337620600591453577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97996371566988268243876205 36748639337620600591453577)
      ·
        refine ⟨27561479503215450443590183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36748639337620600591453577 27561479503215450443590183)
        ·
          refine ⟨41342219254823175665385275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27561479503215450443590183 41342219254823175665385275)
          ·
            refine ⟨62013328882234763498077913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41342219254823175665385275 62013328882234763498077913)
            ·
              refine ⟨46509996661676072623558435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62013328882234763498077913 46509996661676072623558435)
              ·
                refine ⟨69764994992514108935337653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46509996661676072623558435 69764994992514108935337653)
                ·
                  refine ⟨6540468280548197712687905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69764994992514108935337653 6540468280548197712687905)
                  ·
                    refine ⟨4905351210411148284515929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540468280548197712687905 4905351210411148284515929)
                    ·
                      refine ⟨3679013407808361213386947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905351210411148284515929 3679013407808361213386947)
                      ·
                        rfl

theorem cell23_7164853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_7164853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164853 prefixEnd_7164853 := by exact prefixLift 7164853
  have htrace : WordTrace (prefixWord ++ tailWord_7164853) baseStart_7164853 baseEnd_7164853 := by
    simpa [prefixWord, tailWord_7164853, baseEnd_7164853] using wordTrace_append hprefix tailTrace_7164853
  have hstable : (prefixWord ++ tailWord_7164853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164853).length < 2 ^ (prefixWord ++ tailWord_7164853).sum := by decide
  have hdescent : baseEnd_7164853 < baseStart_7164853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164856 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_7164856 : Nat := 118140960795 + 7164856 * 2 ^ 59
def prefixEnd_7164856 : Nat := 4983230072969 + 3 ^ 40 * 7164856 * 2
def baseEnd_7164856 : Nat := 3679014948250324701649433

theorem tailTrace_7164856 : CollatzResearch.WordTrace tailWord_7164856 prefixEnd_7164856 3679014948250324701649433 := by
  unfold tailWord_7164856
  simp only [CollatzResearch.WordTrace]
  refine ⟨130661883465478923414681211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174215844620638564552908281 130661883465478923414681211)
  ·
    refine ⟨195992825198218385122021817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130661883465478923414681211 195992825198218385122021817)
    ·
      refine ⟨146994618898663788841516363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195992825198218385122021817 146994618898663788841516363)
      ·
        refine ⟨220491928347995683262274545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146994618898663788841516363 220491928347995683262274545)
        ·
          refine ⟨165368946260996762446705909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220491928347995683262274545 165368946260996762446705909)
          ·
            refine ⟨15503338711968446479378679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165368946260996762446705909 15503338711968446479378679)
            ·
              refine ⟨23255008067952669719068019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15503338711968446479378679 23255008067952669719068019)
              ·
                refine ⟨34882512101929004578602029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23255008067952669719068019 34882512101929004578602029)
                ·
                  refine ⟨13080942038223376716975761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34882512101929004578602029 13080942038223376716975761)
                  ·
                    refine ⟨9810706528667532537731821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13080942038223376716975761 9810706528667532537731821)
                    ·
                      refine ⟨3679014948250324701649433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9810706528667532537731821 3679014948250324701649433)
                      ·
                        rfl

theorem cell23_7164856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_7164856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164856 prefixEnd_7164856 := by exact prefixLift 7164856
  have htrace : WordTrace (prefixWord ++ tailWord_7164856) baseStart_7164856 baseEnd_7164856 := by
    simpa [prefixWord, tailWord_7164856, baseEnd_7164856] using wordTrace_append hprefix tailTrace_7164856
  have hstable : (prefixWord ++ tailWord_7164856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164856).length < 2 ^ (prefixWord ++ tailWord_7164856).sum := by decide
  have hdescent : baseEnd_7164856 < baseStart_7164856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164889 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_7164889 : Nat := 118140960795 + 7164889 * 2 ^ 59
def prefixEnd_7164889 : Nat := 4983230072969 + 3 ^ 40 * 7164889 * 2
def baseEnd_7164889 : Nat := 1226343964370641024178927

theorem tailTrace_7164889 : CollatzResearch.WordTrace tailWord_7164889 prefixEnd_7164889 1226343964370641024178927 := by
  unfold tailWord_7164889
  simp only [CollatzResearch.WordTrace]
  refine ⟨261324970539838293465313721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174216647026558862310209147 261324970539838293465313721)
  ·
    refine ⟨195993727904878720098985291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261324970539838293465313721 195993727904878720098985291)
    ·
      refine ⟨293990591857318080148477937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195993727904878720098985291 293990591857318080148477937)
      ·
        refine ⟨220492943892988560111358453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293990591857318080148477937 220492943892988560111358453)
        ·
          refine ⟨20671213489967677510439855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220492943892988560111358453 20671213489967677510439855)
          ·
            refine ⟨31006820234951516265659783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20671213489967677510439855 31006820234951516265659783)
            ·
              refine ⟨46510230352427274398489675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31006820234951516265659783 46510230352427274398489675)
              ·
                refine ⟨69765345528640911597734513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46510230352427274398489675 69765345528640911597734513)
                ·
                  refine ⟨52324009146480683698300885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69765345528640911597734513 52324009146480683698300885)
                  ·
                    refine ⟨1226343964370641024178927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52324009146480683698300885 1226343964370641024178927)
                    ·
                      rfl

theorem cell23_7164889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_7164889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164889 prefixEnd_7164889 := by exact prefixLift 7164889
  have htrace : WordTrace (prefixWord ++ tailWord_7164889) baseStart_7164889 baseEnd_7164889 := by
    simpa [prefixWord, tailWord_7164889, baseEnd_7164889] using wordTrace_append hprefix tailTrace_7164889
  have hstable : (prefixWord ++ tailWord_7164889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164889).length < 2 ^ (prefixWord ++ tailWord_7164889).sum := by decide
  have hdescent : baseEnd_7164889 < baseStart_7164889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164903 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7164903 : Nat := 118140960795 + 7164903 * 2 ^ 59
def prefixEnd_7164903 : Nat := 4983230072969 + 3 ^ 40 * 7164903 * 2
def baseEnd_7164903 : Nat := 3679039081841086017761717

theorem tailTrace_7164903 : CollatzResearch.WordTrace tailWord_7164903 prefixEnd_7164903 3679039081841086017761717 := by
  unfold tailWord_7164903
  simp only [CollatzResearch.WordTrace]
  refine ⟨261325481161787573856323363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174216987441191715904215575 261325481161787573856323363)
  ·
    refine ⟨391988221742681360784485045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261325481161787573856323363 391988221742681360784485045)
    ·
      refine ⟨36748895788376377573545473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391988221742681360784485045 36748895788376377573545473)
      ·
        refine ⟨27561671841282283180159105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36748895788376377573545473 27561671841282283180159105)
        ·
          refine ⟨20671253880961712385119329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27561671841282283180159105 20671253880961712385119329)
          ·
            refine ⟨15503440410721284288839497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20671253880961712385119329 15503440410721284288839497)
            ·
              refine ⟨11627580308040963216629623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15503440410721284288839497 11627580308040963216629623)
              ·
                refine ⟨17441370462061444824944435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627580308040963216629623 17441370462061444824944435)
                ·
                  refine ⟨26162055693092167237416653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17441370462061444824944435 26162055693092167237416653)
                  ·
                    refine ⟨9810770884909562714031245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26162055693092167237416653 9810770884909562714031245)
                    ·
                      refine ⟨3679039081841086017761717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9810770884909562714031245 3679039081841086017761717)
                      ·
                        rfl

theorem cell23_7164903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7164903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164903 prefixEnd_7164903 := by exact prefixLift 7164903
  have htrace : WordTrace (prefixWord ++ tailWord_7164903) baseStart_7164903 baseEnd_7164903 := by
    simpa [prefixWord, tailWord_7164903, baseEnd_7164903] using wordTrace_append hprefix tailTrace_7164903
  have hstable : (prefixWord ++ tailWord_7164903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164903).length < 2 ^ (prefixWord ++ tailWord_7164903).sum := by decide
  have hdescent : baseEnd_7164903 < baseStart_7164903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164913 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_7164913 : Nat := 118140960795 + 7164913 * 2 ^ 59
def prefixEnd_7164913 : Nat := 4983230072969 + 3 ^ 40 * 7164913 * 2
def baseEnd_7164913 : Nat := 3679044216647630978636671

theorem tailTrace_7164913 : CollatzResearch.WordTrace tailWord_7164913 prefixEnd_7164913 3679044216647630978636671 := by
  unfold tailWord_7164913
  simp only [CollatzResearch.WordTrace]
  refine ⟨261325845891751345564187393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174217230594500897042791595 261325845891751345564187393)
  ·
    refine ⟨195994384418813509173140545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261325845891751345564187393 195994384418813509173140545)
    ·
      refine ⟨146995788314110131879855409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195994384418813509173140545 146995788314110131879855409)
      ·
        refine ⟨110246841235582598909891557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146995788314110131879855409 110246841235582598909891557)
        ·
          refine ⟨20671282731671737295604667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110246841235582598909891557 20671282731671737295604667)
          ·
            refine ⟨31006924097507605943407001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20671282731671737295604667 31006924097507605943407001)
            ·
              refine ⟨23255193073130704457555251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31006924097507605943407001 23255193073130704457555251)
              ·
                refine ⟨34882789609696056686332877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23255193073130704457555251 34882789609696056686332877)
                ·
                  refine ⟨13081046103636021257374829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34882789609696056686332877 13081046103636021257374829)
                  ·
                    refine ⟨4905392288863507971515561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13081046103636021257374829 4905392288863507971515561)
                    ·
                      refine ⟨3679044216647630978636671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905392288863507971515561 3679044216647630978636671)
                      ·
                        rfl

theorem cell23_7164913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_7164913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7164913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7164913 prefixEnd_7164913 := by exact prefixLift 7164913
  have htrace : WordTrace (prefixWord ++ tailWord_7164913) baseStart_7164913 baseEnd_7164913 := by
    simpa [prefixWord, tailWord_7164913, baseEnd_7164913] using wordTrace_append hprefix tailTrace_7164913
  have hstable : (prefixWord ++ tailWord_7164913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164913).length < 2 ^ (prefixWord ++ tailWord_7164913).sum := by decide
  have hdescent : baseEnd_7164913 < baseStart_7164913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165006 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7165006 : Nat := 118140960795 + 7165006 * 2 ^ 59
def prefixEnd_7165006 : Nat := 4983230072969 + 3 ^ 40 * 7165006 * 2
def baseEnd_7165006 : Nat := 3679091970348499114773743

theorem tailTrace_7165006 : CollatzResearch.WordTrace tailWord_7165006 prefixEnd_7165006 3679091970348499114773743 := by
  unfold tailWord_7165006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666154735051802805915359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174219491920276281631548581 32666154735051802805915359)
  ·
    refine ⟨48999232102577704208873039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32666154735051802805915359 48999232102577704208873039)
    ·
      refine ⟨73498848153866556313309559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48999232102577704208873039 73498848153866556313309559)
      ·
        refine ⟨110248272230799834469964339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73498848153866556313309559 110248272230799834469964339)
        ·
          refine ⟨165372408346199751704946509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110248272230799834469964339 165372408346199751704946509)
          ·
            refine ⟨62014653129824906889354941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165372408346199751704946509 62014653129824906889354941)
            ·
              refine ⟨23255494923684340083508103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62014653129824906889354941 23255494923684340083508103)
              ·
                refine ⟨34883242385526510125262155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23255494923684340083508103 34883242385526510125262155)
                ·
                  refine ⟨52324863578289765187893233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34883242385526510125262155 52324863578289765187893233)
                  ·
                    refine ⟨39243647683717323890919925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52324863578289765187893233 39243647683717323890919925)
                    ·
                      refine ⟨3679091970348499114773743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39243647683717323890919925 3679091970348499114773743)
                      ·
                        rfl

theorem cell23_7165006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7165006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165006 prefixEnd_7165006 := by exact prefixLift 7165006
  have htrace : WordTrace (prefixWord ++ tailWord_7165006) baseStart_7165006 baseEnd_7165006 := by
    simpa [prefixWord, tailWord_7165006, baseEnd_7165006] using wordTrace_append hprefix tailTrace_7165006
  have hstable : (prefixWord ++ tailWord_7165006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165006).length < 2 ^ (prefixWord ++ tailWord_7165006).sum := by decide
  have hdescent : baseEnd_7165006 < baseStart_7165006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165016 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7165016 : Nat := 118140960795 + 7165016 * 2 ^ 59
def prefixEnd_7165016 : Nat := 4983230072969 + 3 ^ 40 * 7165016 * 2
def baseEnd_7165016 : Nat := 3679097105155044075648697

theorem tailTrace_7165016 : CollatzResearch.WordTrace tailWord_7165016 prefixEnd_7165016 3679097105155044075648697 := by
  unfold tailWord_7165016
  simp only [CollatzResearch.WordTrace]
  refine ⟨130664801305189097077593451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174219735073585462770124601 130664801305189097077593451)
  ·
    refine ⟨195997201957783645616390177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130664801305189097077593451 195997201957783645616390177)
    ·
      refine ⟨146997901468337734212292633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195997201957783645616390177 146997901468337734212292633)
      ·
        refine ⟨110248426101253300659219475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146997901468337734212292633 110248426101253300659219475)
        ·
          refine ⟨165372639151879950988829213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110248426101253300659219475 165372639151879950988829213)
          ·
            refine ⟨62014739681954981620810955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165372639151879950988829213 62014739681954981620810955)
            ·
              refine ⟨93022109522932472431216433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62014739681954981620810955 93022109522932472431216433)
              ·
                refine ⟨69766582142199354323412325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93022109522932472431216433 69766582142199354323412325)
                ·
                  refine ⟨13081234151662378935639811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69766582142199354323412325 13081234151662378935639811)
                  ·
                    refine ⟨19621851227493568403459717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13081234151662378935639811 19621851227493568403459717)
                    ·
                      refine ⟨3679097105155044075648697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19621851227493568403459717 3679097105155044075648697)
                      ·
                        rfl

theorem cell23_7165016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7165016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165016 prefixEnd_7165016 := by exact prefixLift 7165016
  have htrace : WordTrace (prefixWord ++ tailWord_7165016) baseStart_7165016 baseEnd_7165016 := by
    simpa [prefixWord, tailWord_7165016, baseEnd_7165016] using wordTrace_append hprefix tailTrace_7165016
  have hstable : (prefixWord ++ tailWord_7165016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165016).length < 2 ^ (prefixWord ++ tailWord_7165016).sum := by decide
  have hdescent : baseEnd_7165016 < baseStart_7165016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165033 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_7165033 : Nat := 118140960795 + 7165033 * 2 ^ 59
def prefixEnd_7165033 : Nat := 4983230072969 + 3 ^ 40 * 7165033 * 2
def baseEnd_7165033 : Nat := 3679105834326170509136119

theorem tailTrace_7165033 : CollatzResearch.WordTrace tailWord_7165033 prefixEnd_7165033 3679105834326170509136119 := by
  unfold tailWord_7165033
  simp only [CollatzResearch.WordTrace]
  refine ⟨261330222651316606058555753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174220148434211070705703835 261330222651316606058555753)
  ·
    refine ⟨195997666988487454543916815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261330222651316606058555753 195997666988487454543916815)
    ·
      refine ⟨293996500482731181815875223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195997666988487454543916815 293996500482731181815875223)
      ·
        refine ⟨440994750724096772723812835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293996500482731181815875223 440994750724096772723812835)
        ·
          refine ⟨661492126086145159085719253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440994750724096772723812835 661492126086145159085719253)
          ·
            refine ⟨15503721705144027166071545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 661492126086145159085719253 15503721705144027166071545)
            ·
              refine ⟨11627791278858020374553659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15503721705144027166071545 11627791278858020374553659)
              ·
                refine ⟨17441686918287030561830489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627791278858020374553659 17441686918287030561830489)
                ·
                  refine ⟨13081265188715272921372867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17441686918287030561830489 13081265188715272921372867)
                  ·
                    refine ⟨19621897783072909382059301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13081265188715272921372867 19621897783072909382059301)
                    ·
                      refine ⟨3679105834326170509136119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19621897783072909382059301 3679105834326170509136119)
                      ·
                        rfl

theorem cell23_7165033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_7165033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165033 prefixEnd_7165033 := by exact prefixLift 7165033
  have htrace : WordTrace (prefixWord ++ tailWord_7165033) baseStart_7165033 baseEnd_7165033 := by
    simpa [prefixWord, tailWord_7165033, baseEnd_7165033] using wordTrace_append hprefix tailTrace_7165033
  have hstable : (prefixWord ++ tailWord_7165033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165033).length < 2 ^ (prefixWord ++ tailWord_7165033).sum := by decide
  have hdescent : baseEnd_7165033 < baseStart_7165033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165053 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_7165053 : Nat := 118140960795 + 7165053 * 2 ^ 59
def prefixEnd_7165053 : Nat := 4983230072969 + 3 ^ 40 * 7165053 * 2
def baseEnd_7165053 : Nat := 3679116103939260430886027

theorem tailTrace_7165053 : CollatzResearch.WordTrace tailWord_7165053 prefixEnd_7165053 3679116103939260430886027 := by
  unfold tailWord_7165053
  simp only [CollatzResearch.WordTrace]
  refine ⟨261330952111244149474283813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174220634740829432982855875 261330952111244149474283813)
  ·
    refine ⟨48999553520858278026428215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261330952111244149474283813 48999553520858278026428215)
    ·
      refine ⟨73499330281287417039642323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48999553520858278026428215 73499330281287417039642323)
      ·
        refine ⟨110248995421931125559463485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73499330281287417039642323 110248995421931125559463485)
        ·
          refine ⟨41343373283224172084798807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110248995421931125559463485 41343373283224172084798807)
          ·
            refine ⟨62015059924836258127198211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343373283224172084798807 62015059924836258127198211)
            ·
              refine ⟨93022589887254387190797317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62015059924836258127198211 93022589887254387190797317)
              ·
                refine ⟨17441735603860197598274497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93022589887254387190797317 17441735603860197598274497)
                ·
                  refine ⟨13081301702895148198705873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17441735603860197598274497 13081301702895148198705873)
                  ·
                    refine ⟨9810976277171361149029405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13081301702895148198705873 9810976277171361149029405)
                    ·
                      refine ⟨3679116103939260430886027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9810976277171361149029405 3679116103939260430886027)
                      ·
                        rfl

theorem cell23_7165053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_7165053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165053 prefixEnd_7165053 := by exact prefixLift 7165053
  have htrace : WordTrace (prefixWord ++ tailWord_7165053) baseStart_7165053 baseEnd_7165053 := by
    simpa [prefixWord, tailWord_7165053, baseEnd_7165053] using wordTrace_append hprefix tailTrace_7165053
  have hstable : (prefixWord ++ tailWord_7165053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165053).length < 2 ^ (prefixWord ++ tailWord_7165053).sum := by decide
  have hdescent : baseEnd_7165053 < baseStart_7165053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165056 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 6]
def baseStart_7165056 : Nat := 118140960795 + 7165056 * 2 ^ 59
def prefixEnd_7165056 : Nat := 4983230072969 + 3 ^ 40 * 7165056 * 2
def baseEnd_7165056 : Nat := 408790849375691546572057

theorem tailTrace_7165056 : CollatzResearch.WordTrace tailWord_7165056 prefixEnd_7165056 408790849375691546572057 := by
  unfold tailWord_7165056
  simp only [CollatzResearch.WordTrace]
  refine ⟨130665530765116640493321511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174220707686822187324428681 130665530765116640493321511)
  ·
    refine ⟨195998296147674960739982267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130665530765116640493321511 195998296147674960739982267)
    ·
      refine ⟨293997444221512441109973401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195998296147674960739982267 293997444221512441109973401)
      ·
        refine ⟨220498083166134330832480051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293997444221512441109973401 220498083166134330832480051)
        ·
          refine ⟨330747124749201496248720077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220498083166134330832480051 330747124749201496248720077)
          ·
            refine ⟨124030171780950561093270029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330747124749201496248720077 124030171780950561093270029)
            ·
              refine ⟨46511314417856460409976261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124030171780950561093270029 46511314417856460409976261)
              ·
                refine ⟨8720871453348086326870549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46511314417856460409976261 8720871453348086326870549)
                ·
                  refine ⟨408790849375691546572057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8720871453348086326870549 408790849375691546572057)
                  ·
                    rfl

theorem cell23_7165056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_7165056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165056 prefixEnd_7165056 := by exact prefixLift 7165056
  have htrace : WordTrace (prefixWord ++ tailWord_7165056) baseStart_7165056 baseEnd_7165056 := by
    simpa [prefixWord, tailWord_7165056, baseEnd_7165056] using wordTrace_append hprefix tailTrace_7165056
  have hstable : (prefixWord ++ tailWord_7165056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165056).length < 2 ^ (prefixWord ++ tailWord_7165056).sum := by decide
  have hdescent : baseEnd_7165056 < baseStart_7165056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165087 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7165087 : Nat := 118140960795 + 7165087 * 2 ^ 59
def prefixEnd_7165087 : Nat := 4983230072969 + 3 ^ 40 * 7165087 * 2
def baseEnd_7165087 : Nat := 3679133562281513297860871

theorem tailTrace_7165087 : CollatzResearch.WordTrace tailWord_7165087 prefixEnd_7165087 3679133562281513297860871 := by
  unfold tailWord_7165087
  simp only [CollatzResearch.WordTrace]
  refine ⟨261332192193120973281021515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174221461462080648854014343 261332192193120973281021515)
  ·
    refine ⟨391998288289681459921532273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261332192193120973281021515 391998288289681459921532273)
    ·
      refine ⟨293998716217261094941149205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391998288289681459921532273 293998716217261094941149205)
      ·
        refine ⟨13781189822684113825366369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293998716217261094941149205 13781189822684113825366369)
        ·
          refine ⟨10335892367013085369024777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13781189822684113825366369 10335892367013085369024777)
          ·
            refine ⟨7751919275259814026768583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335892367013085369024777 7751919275259814026768583)
            ·
              refine ⟨11627878912889721040152875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751919275259814026768583 11627878912889721040152875)
              ·
                refine ⟨17441818369334581560229313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627878912889721040152875 17441818369334581560229313)
                ·
                  refine ⟨13081363777000936170171985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17441818369334581560229313 13081363777000936170171985)
                  ·
                    refine ⟨9811022832750702127628989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13081363777000936170171985 9811022832750702127628989)
                    ·
                      refine ⟨3679133562281513297860871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811022832750702127628989 3679133562281513297860871)
                      ·
                        rfl

theorem cell23_7165087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7165087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165087 prefixEnd_7165087 := by exact prefixLift 7165087
  have htrace : WordTrace (prefixWord ++ tailWord_7165087) baseStart_7165087 baseEnd_7165087 := by
    simpa [prefixWord, tailWord_7165087, baseEnd_7165087] using wordTrace_append hprefix tailTrace_7165087
  have hstable : (prefixWord ++ tailWord_7165087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165087).length < 2 ^ (prefixWord ++ tailWord_7165087).sum := by decide
  have hdescent : baseEnd_7165087 < baseStart_7165087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165117 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_7165117 : Nat := 118140960795 + 7165117 * 2 ^ 59
def prefixEnd_7165117 : Nat := 4983230072969 + 3 ^ 40 * 7165117 * 2
def baseEnd_7165117 : Nat := 3679148966701148180485733

theorem tailTrace_7165117 : CollatzResearch.WordTrace tailWord_7165117 prefixEnd_7165117 3679148966701148180485733 := by
  unfold tailWord_7165117
  simp only [CollatzResearch.WordTrace]
  refine ⟨261333286383012288404613605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174222190922008192269742403 261333286383012288404613605)
  ·
    refine ⟨48999991196814804075865051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261333286383012288404613605 48999991196814804075865051)
    ·
      refine ⟨73499986795222206113797577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48999991196814804075865051 73499986795222206113797577)
      ·
        refine ⟨55124990096416654585348183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73499986795222206113797577 55124990096416654585348183)
        ·
          refine ⟨82687485144624981878022275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55124990096416654585348183 82687485144624981878022275)
          ·
            refine ⟨124031227716937472817033413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82687485144624981878022275 124031227716937472817033413)
            ·
              refine ⟨23255855196925776153193765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124031227716937472817033413 23255855196925776153193765)
              ·
                refine ⟨4360472849423583028723831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23255855196925776153193765 4360472849423583028723831)
                ·
                  refine ⟨6540709274135374543085747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360472849423583028723831 6540709274135374543085747)
                  ·
                    refine ⟨9811063911203061814628621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6540709274135374543085747 9811063911203061814628621)
                    ·
                      refine ⟨3679148966701148180485733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811063911203061814628621 3679148966701148180485733)
                      ·
                        rfl

theorem cell23_7165117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_7165117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165117 prefixEnd_7165117 := by exact prefixLift 7165117
  have htrace : WordTrace (prefixWord ++ tailWord_7165117) baseStart_7165117 baseEnd_7165117 := by
    simpa [prefixWord, tailWord_7165117, baseEnd_7165117] using wordTrace_append hprefix tailTrace_7165117
  have hstable : (prefixWord ++ tailWord_7165117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165117).length < 2 ^ (prefixWord ++ tailWord_7165117).sum := by decide
  have hdescent : baseEnd_7165117 < baseStart_7165117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165143 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_7165143 : Nat := 118140960795 + 7165143 * 2 ^ 59
def prefixEnd_7165143 : Nat := 4983230072969 + 3 ^ 40 * 7165143 * 2
def baseEnd_7165143 : Nat := 3679162317198165078760613

theorem tailTrace_7165143 : CollatzResearch.WordTrace tailWord_7165143 prefixEnd_7165143 3679162317198165078760613 := by
  unfold tailWord_7165143
  simp only [CollatzResearch.WordTrace]
  refine ⟨261334234680918094845060083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174222823120612063230040055 261334234680918094845060083)
  ·
    refine ⟨392001352021377142267590125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261334234680918094845060083 392001352021377142267590125)
    ·
      refine ⟨147000507008016428350346297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392001352021377142267590125 147000507008016428350346297)
      ·
        refine ⟨110250380256012321262759723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147000507008016428350346297 110250380256012321262759723)
        ·
          refine ⟨165375570384018481894139585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110250380256012321262759723 165375570384018481894139585)
          ·
            refine ⟨124031677788013861420604689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165375570384018481894139585 124031677788013861420604689)
            ·
              refine ⟨93023758341010396065453517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124031677788013861420604689 93023758341010396065453517)
              ·
                refine ⟨34883909377878898524545069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93023758341010396065453517 34883909377878898524545069)
                ·
                  refine ⟨13081466016704586946704401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34883909377878898524545069 13081466016704586946704401)
                  ·
                    refine ⟨9811099512528440210028301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13081466016704586946704401 9811099512528440210028301)
                    ·
                      refine ⟨3679162317198165078760613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811099512528440210028301 3679162317198165078760613)
                      ·
                        rfl

theorem cell23_7165143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_7165143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165143 prefixEnd_7165143 := by exact prefixLift 7165143
  have htrace : WordTrace (prefixWord ++ tailWord_7165143) baseStart_7165143 baseEnd_7165143 := by
    simpa [prefixWord, tailWord_7165143, baseEnd_7165143] using wordTrace_append hprefix tailTrace_7165143
  have hstable : (prefixWord ++ tailWord_7165143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165143).length < 2 ^ (prefixWord ++ tailWord_7165143).sum := by decide
  have hdescent : baseEnd_7165143 < baseStart_7165143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165160 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7165160 : Nat := 118140960795 + 7165160 * 2 ^ 59
def prefixEnd_7165160 : Nat := 4983230072969 + 3 ^ 40 * 7165160 * 2
def baseEnd_7165160 : Nat := 3679171046369291512248035

theorem tailTrace_7165160 : CollatzResearch.WordTrace tailWord_7165160 prefixEnd_7165160 3679171046369291512248035 := by
  unfold tailWord_7165160
  simp only [CollatzResearch.WordTrace]
  refine ⟨130667427360928253374214467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174223236481237671165619289 130667427360928253374214467)
  ·
    refine ⟨196001141041392380061321701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130667427360928253374214467 196001141041392380061321701)
    ·
      refine ⟨36750213945261071261497819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196001141041392380061321701 36750213945261071261497819)
      ·
        refine ⟨55125320917891606892246729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36750213945261071261497819 55125320917891606892246729)
        ·
          refine ⟨41343990688418705169185047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55125320917891606892246729 41343990688418705169185047)
          ·
            refine ⟨62015986032628057753777571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343990688418705169185047 62015986032628057753777571)
            ·
              refine ⟨93023979048942086630666357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62015986032628057753777571 93023979048942086630666357)
              ·
                refine ⟨8720998035838320621624971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93023979048942086630666357 8720998035838320621624971)
                ·
                  refine ⟨13081497053757480932437457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720998035838320621624971 13081497053757480932437457)
                  ·
                    refine ⟨9811122790318110699328093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13081497053757480932437457 9811122790318110699328093)
                    ·
                      refine ⟨3679171046369291512248035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811122790318110699328093 3679171046369291512248035)
                      ·
                        rfl

theorem cell23_7165160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7165160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165160 prefixEnd_7165160 := by exact prefixLift 7165160
  have htrace : WordTrace (prefixWord ++ tailWord_7165160) baseStart_7165160 baseEnd_7165160 := by
    simpa [prefixWord, tailWord_7165160, baseEnd_7165160] using wordTrace_append hprefix tailTrace_7165160
  have hstable : (prefixWord ++ tailWord_7165160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165160).length < 2 ^ (prefixWord ++ tailWord_7165160).sum := by decide
  have hdescent : baseEnd_7165160 < baseStart_7165160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165224 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7165224 : Nat := 118140960795 + 7165224 * 2 ^ 59
def prefixEnd_7165224 : Nat := 4983230072969 + 3 ^ 40 * 7165224 * 2
def baseEnd_7165224 : Nat := 3679203909131179261847741

theorem tailTrace_7165224 : CollatzResearch.WordTrace tailWord_7165224 prefixEnd_7165224 3679203909131179261847741 := by
  unfold tailWord_7165224
  simp only [CollatzResearch.WordTrace]
  refine ⟨130668594496812322839379363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174224792662416430452505817 130668594496812322839379363)
  ·
    refine ⟨196002891745218484259069045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130668594496812322839379363 196002891745218484259069045)
    ·
      refine ⟨18375271101114232899287723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196002891745218484259069045 18375271101114232899287723)
      ·
        refine ⟨27562906651671349348931585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375271101114232899287723 27562906651671349348931585)
        ·
          refine ⟨20672179988753512011698689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27562906651671349348931585 20672179988753512011698689)
          ·
            refine ⟨15504134991565134008774017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20672179988753512011698689 15504134991565134008774017)
            ·
              refine ⟨11628101243673850506580513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504134991565134008774017 11628101243673850506580513)
              ·
                refine ⟨8721075932755387879935385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11628101243673850506580513 8721075932755387879935385)
                ·
                  refine ⟨6540806949566540909951539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8721075932755387879935385 6540806949566540909951539)
                  ·
                    refine ⟨9811210424349811364927309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6540806949566540909951539 9811210424349811364927309)
                    ·
                      refine ⟨3679203909131179261847741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811210424349811364927309 3679203909131179261847741)
                      ·
                        rfl

theorem cell23_7165224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7165224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165224 prefixEnd_7165224 := by exact prefixLift 7165224
  have htrace : WordTrace (prefixWord ++ tailWord_7165224) baseStart_7165224 baseEnd_7165224 := by
    simpa [prefixWord, tailWord_7165224, baseEnd_7165224] using wordTrace_append hprefix tailTrace_7165224
  have hstable : (prefixWord ++ tailWord_7165224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165224).length < 2 ^ (prefixWord ++ tailWord_7165224).sum := by decide
  have hdescent : baseEnd_7165224 < baseStart_7165224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165247 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 4, 2]
def baseStart_7165247 : Nat := 118140960795 + 7165247 * 2 ^ 59
def prefixEnd_7165247 : Nat := 4983230072969 + 3 ^ 40 * 7165247 * 2
def baseEnd_7165247 : Nat := 3679215719186232671860135

theorem tailTrace_7165247 : CollatzResearch.WordTrace tailWord_7165247 prefixEnd_7165247 3679215719186232671860135 := by
  unfold tailWord_7165247
  simp only [CollatzResearch.WordTrace]
  refine ⟨261338027872541320606845995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174225351915027547071230663 261338027872541320606845995)
  ·
    refine ⟨392007041808811980910268993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261338027872541320606845995 392007041808811980910268993)
    ·
      refine ⟨294005281356608985682701745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392007041808811980910268993 294005281356608985682701745)
      ·
        refine ⟨220503961017456739262026309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294005281356608985682701745 220503961017456739262026309)
        ·
          refine ⟨41344492690773138611629933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220503961017456739262026309 41344492690773138611629933)
          ·
            refine ⟨15504184759039926979361225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41344492690773138611629933 15504184759039926979361225)
            ·
              refine ⟨11628138569279945234520919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504184759039926979361225 11628138569279945234520919)
              ·
                refine ⟨17442207853919917851781379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628138569279945234520919 17442207853919917851781379)
                ·
                  refine ⟨26163311780879876777672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17442207853919917851781379 26163311780879876777672069)
                  ·
                    refine ⟨4905620958914976895813513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26163311780879876777672069 4905620958914976895813513)
                    ·
                      refine ⟨3679215719186232671860135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905620958914976895813513 3679215719186232671860135)
                      ·
                        rfl

theorem cell23_7165247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_7165247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165247 prefixEnd_7165247 := by exact prefixLift 7165247
  have htrace : WordTrace (prefixWord ++ tailWord_7165247) baseStart_7165247 baseEnd_7165247 := by
    simpa [prefixWord, tailWord_7165247, baseEnd_7165247] using wordTrace_append hprefix tailTrace_7165247
  have hstable : (prefixWord ++ tailWord_7165247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165247).length < 2 ^ (prefixWord ++ tailWord_7165247).sum := by decide
  have hdescent : baseEnd_7165247 < baseStart_7165247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165280 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_7165280 : Nat := 118140960795 + 7165280 * 2 ^ 59
def prefixEnd_7165280 : Nat := 4983230072969 + 3 ^ 40 * 7165280 * 2
def baseEnd_7165280 : Nat := 3679232664047831042747483

theorem tailTrace_7165280 : CollatzResearch.WordTrace tailWord_7165280 prefixEnd_7165280 3679232664047831042747483 := by
  unfold tailWord_7165280
  simp only [CollatzResearch.WordTrace]
  refine ⟨130669615740710883621398647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174226154320947844828531529 130669615740710883621398647)
  ·
    refine ⟨196004423611066325432097971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130669615740710883621398647 196004423611066325432097971)
    ·
      refine ⟨294006635416599488148146957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196004423611066325432097971 294006635416599488148146957)
      ·
        refine ⟨110252488281224808055555109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294006635416599488148146957 110252488281224808055555109)
        ·
          refine ⟨20672341552729651510416583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110252488281224808055555109 20672341552729651510416583)
          ·
            refine ⟨31008512329094477265624875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20672341552729651510416583 31008512329094477265624875)
            ·
              refine ⟨46512768493641715898437313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31008512329094477265624875 46512768493641715898437313)
              ·
                refine ⟨34884576370231286923827985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46512768493641715898437313 34884576370231286923827985)
                ·
                  refine ⟨26163432277673465192870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34884576370231286923827985 26163432277673465192870989)
                  ·
                    refine ⟨9811287104127549447326621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26163432277673465192870989 9811287104127549447326621)
                    ·
                      refine ⟨3679232664047831042747483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811287104127549447326621 3679232664047831042747483)
                      ·
                        rfl

theorem cell23_7165280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_7165280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165280 prefixEnd_7165280 := by exact prefixLift 7165280
  have htrace : WordTrace (prefixWord ++ tailWord_7165280) baseStart_7165280 baseEnd_7165280 := by
    simpa [prefixWord, tailWord_7165280, baseEnd_7165280] using wordTrace_append hprefix tailTrace_7165280
  have hstable : (prefixWord ++ tailWord_7165280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165280).length < 2 ^ (prefixWord ++ tailWord_7165280).sum := by decide
  have hdescent : baseEnd_7165280 < baseStart_7165280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165303 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_7165303 : Nat := 118140960795 + 7165303 * 2 ^ 59
def prefixEnd_7165303 : Nat := 4983230072969 + 3 ^ 40 * 7165303 * 2
def baseEnd_7165303 : Nat := 3679244474102884452759877

theorem tailTrace_7165303 : CollatzResearch.WordTrace tailWord_7165303 prefixEnd_7165303 3679244474102884452759877 := by
  unfold tailWord_7165303
  simp only [CollatzResearch.WordTrace]
  refine ⟨261340070360338442170884563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174226713573558961447256375 261340070360338442170884563)
  ·
    refine ⟨392010105540507663256326845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261340070360338442170884563 392010105540507663256326845)
    ·
      refine ⟨147003789577690373721122567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392010105540507663256326845 147003789577690373721122567)
      ·
        refine ⟨220505684366535560581683851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147003789577690373721122567 220505684366535560581683851)
        ·
          refine ⟨330758526549803340872525777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220505684366535560581683851 330758526549803340872525777)
          ·
            refine ⟨248068894912352505654394333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330758526549803340872525777 248068894912352505654394333)
            ·
              refine ⟨93025835592132189620397875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248068894912352505654394333 93025835592132189620397875)
              ·
                refine ⟨139538753388198284430596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93025835592132189620397875 139538753388198284430596813)
                ·
                  refine ⟨52327032520574356661473805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139538753388198284430596813 52327032520574356661473805)
                  ·
                    refine ⟨19622637195215383748052677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52327032520574356661473805 19622637195215383748052677)
                    ·
                      refine ⟨3679244474102884452759877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19622637195215383748052677 3679244474102884452759877)
                      ·
                        rfl

theorem cell23_7165303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_7165303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165303 prefixEnd_7165303 := by exact prefixLift 7165303
  have htrace : WordTrace (prefixWord ++ tailWord_7165303) baseStart_7165303 baseEnd_7165303 := by
    simpa [prefixWord, tailWord_7165303, baseEnd_7165303] using wordTrace_append hprefix tailTrace_7165303
  have hstable : (prefixWord ++ tailWord_7165303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165303).length < 2 ^ (prefixWord ++ tailWord_7165303).sum := by decide
  have hdescent : baseEnd_7165303 < baseStart_7165303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165320 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7165320 : Nat := 118140960795 + 7165320 * 2 ^ 59
def prefixEnd_7165320 : Nat := 4983230072969 + 3 ^ 40 * 7165320 * 2
def baseEnd_7165320 : Nat := 3679253203274010886247299

theorem tailTrace_7165320 : CollatzResearch.WordTrace tailWord_7165320 prefixEnd_7165320 3679253203274010886247299 := by
  unfold tailWord_7165320
  simp only [CollatzResearch.WordTrace]
  refine ⟨130670345200638427037126707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174227126934184569382835609 130670345200638427037126707)
  ·
    refine ⟨196005517800957640555690061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130670345200638427037126707 196005517800957640555690061)
    ·
      refine ⟨73502069175359115208383773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196005517800957640555690061 73502069175359115208383773)
      ·
        refine ⟨27563275940759668203143915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73502069175359115208383773 27563275940759668203143915)
        ·
          refine ⟨41344913911139502304715873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27563275940759668203143915 41344913911139502304715873)
          ·
            refine ⟨31008685433354626728536905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41344913911139502304715873 31008685433354626728536905)
            ·
              refine ⟨23256514075015970046402679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31008685433354626728536905 23256514075015970046402679)
              ·
                refine ⟨34884771112523955069604019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23256514075015970046402679 34884771112523955069604019)
                ·
                  refine ⟨52327156668785932604406029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34884771112523955069604019 52327156668785932604406029)
                  ·
                    refine ⟨19622683750794724726652261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52327156668785932604406029 19622683750794724726652261)
                    ·
                      refine ⟨3679253203274010886247299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19622683750794724726652261 3679253203274010886247299)
                      ·
                        rfl

theorem cell23_7165320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7165320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165320 prefixEnd_7165320 := by exact prefixLift 7165320
  have htrace : WordTrace (prefixWord ++ tailWord_7165320) baseStart_7165320 baseEnd_7165320 := by
    simpa [prefixWord, tailWord_7165320, baseEnd_7165320] using wordTrace_append hprefix tailTrace_7165320
  have hstable : (prefixWord ++ tailWord_7165320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165320).length < 2 ^ (prefixWord ++ tailWord_7165320).sum := by decide
  have hdescent : baseEnd_7165320 < baseStart_7165320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165333 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7165333 : Nat := 118140960795 + 7165333 * 2 ^ 59
def prefixEnd_7165333 : Nat := 4983230072969 + 3 ^ 40 * 7165333 * 2
def baseEnd_7165333 : Nat := 3679259878522519335384739

theorem tailTrace_7165333 : CollatzResearch.WordTrace tailWord_7165333 prefixEnd_7165333 3679259878522519335384739 := by
  unfold tailWord_7165333
  simp only [CollatzResearch.WordTrace]
  refine ⟨261341164550229757294476653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174227443033486504862984435 261341164550229757294476653)
  ·
    refine ⟨98002936706336158985428745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261341164550229757294476653 98002936706336158985428745)
    ·
      refine ⟨73502202529752119239071559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98002936706336158985428745 73502202529752119239071559)
      ·
        refine ⟨110253303794628178858607339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73502202529752119239071559 110253303794628178858607339)
        ·
          refine ⟨165379955691942268287911009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110253303794628178858607339 165379955691942268287911009)
          ·
            refine ⟨124034966768956701215933257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165379955691942268287911009 124034966768956701215933257)
            ·
              refine ⟨93026225076717525911949943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124034966768956701215933257 93026225076717525911949943)
              ·
                refine ⟨139539337615076288867924915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93026225076717525911949943 139539337615076288867924915)
                ·
                  refine ⟨209309006422614433301887373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139539337615076288867924915 209309006422614433301887373)
                  ·
                    refine ⟨78490877408480412488207765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209309006422614433301887373 78490877408480412488207765)
                    ·
                      refine ⟨3679259878522519335384739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78490877408480412488207765 3679259878522519335384739)
                      ·
                        rfl

theorem cell23_7165333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7165333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165333 prefixEnd_7165333 := by exact prefixLift 7165333
  have htrace : WordTrace (prefixWord ++ tailWord_7165333) baseStart_7165333 baseEnd_7165333 := by
    simpa [prefixWord, tailWord_7165333, baseEnd_7165333] using wordTrace_append hprefix tailTrace_7165333
  have hstable : (prefixWord ++ tailWord_7165333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165333).length < 2 ^ (prefixWord ++ tailWord_7165333).sum := by decide
  have hdescent : baseEnd_7165333 < baseStart_7165333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165363 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_7165363 : Nat := 118140960795 + 7165363 * 2 ^ 59
def prefixEnd_7165363 : Nat := 4983230072969 + 3 ^ 40 * 7165363 * 2
def baseEnd_7165363 : Nat := 3679275282942154218009601

theorem tailTrace_7165363 : CollatzResearch.WordTrace tailWord_7165363 prefixEnd_7165363 3679275282942154218009601 := by
  unfold tailWord_7165363
  simp only [CollatzResearch.WordTrace]
  refine ⟨261342258740121072418068743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174228172493414048278712495 261342258740121072418068743)
  ·
    refine ⟨392013388110181608627103115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261342258740121072418068743 392013388110181608627103115)
    ·
      refine ⟨588020082165272412940654673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392013388110181608627103115 588020082165272412940654673)
      ·
        refine ⟨441015061623954309705491005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588020082165272412940654673 441015061623954309705491005)
        ·
          refine ⟨165380648108982866139559127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441015061623954309705491005 165380648108982866139559127)
          ·
            refine ⟨248070972163474299209338691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165380648108982866139559127 248070972163474299209338691)
            ·
              refine ⟨372106458245211448814008037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248070972163474299209338691 372106458245211448814008037)
              ·
                refine ⟨69769960920977146652626507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372106458245211448814008037 69769960920977146652626507)
                ·
                  refine ⟨104654941381465719978939761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69769960920977146652626507 104654941381465719978939761)
                  ·
                    refine ⟨78491206036099289984204821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104654941381465719978939761 78491206036099289984204821)
                    ·
                      refine ⟨3679275282942154218009601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78491206036099289984204821 3679275282942154218009601)
                      ·
                        rfl

theorem cell23_7165363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_7165363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165363 prefixEnd_7165363 := by exact prefixLift 7165363
  have htrace : WordTrace (prefixWord ++ tailWord_7165363) baseStart_7165363 baseEnd_7165363 := by
    simpa [prefixWord, tailWord_7165363, baseEnd_7165363] using wordTrace_append hprefix tailTrace_7165363
  have hstable : (prefixWord ++ tailWord_7165363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165363).length < 2 ^ (prefixWord ++ tailWord_7165363).sum := by decide
  have hdescent : baseEnd_7165363 < baseStart_7165363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165398 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7165398 : Nat := 118140960795 + 7165398 * 2 ^ 59
def prefixEnd_7165398 : Nat := 4983230072969 + 3 ^ 40 * 7165398 * 2
def baseEnd_7165398 : Nat := 1226431084921687193690647

theorem tailTrace_7165398 : CollatzResearch.WordTrace tailWord_7165398 prefixEnd_7165398 1226431084921687193690647 := by
  unfold tailWord_7165398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333970955937142087224553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174229023529996182263728565 16333970955937142087224553)
  ·
    refine ⟨12250478216952856565418415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16333970955937142087224553 12250478216952856565418415)
    ·
      refine ⟨18375717325429284848127623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250478216952856565418415 18375717325429284848127623)
      ·
        refine ⟨27563575988143927272191435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375717325429284848127623 27563575988143927272191435)
        ·
          refine ⟨41345363982215890908287153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27563575988143927272191435 41345363982215890908287153)
          ·
            refine ⟨31009022986661918181215365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41345363982215890908287153 31009022986661918181215365)
            ·
              refine ⟨5814191809999109658977881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31009022986661918181215365 5814191809999109658977881)
              ·
                refine ⟨4360643857499332244233411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814191809999109658977881 4360643857499332244233411)
                ·
                  refine ⟨6540965786248998366350117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360643857499332244233411 6540965786248998366350117)
                  ·
                    refine ⟨1226431084921687193690647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540965786248998366350117 1226431084921687193690647)
                    ·
                      rfl

theorem cell23_7165398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7165398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165398 prefixEnd_7165398 := by exact prefixLift 7165398
  have htrace : WordTrace (prefixWord ++ tailWord_7165398) baseStart_7165398 baseEnd_7165398 := by
    simpa [prefixWord, tailWord_7165398, baseEnd_7165398] using wordTrace_append hprefix tailTrace_7165398
  have hstable : (prefixWord ++ tailWord_7165398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165398).length < 2 ^ (prefixWord ++ tailWord_7165398).sum := by decide
  have hdescent : baseEnd_7165398 < baseStart_7165398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165421 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7165421 : Nat := 118140960795 + 7165421 * 2 ^ 59
def prefixEnd_7165421 : Nat := 4983230072969 + 3 ^ 40 * 7165421 * 2
def baseEnd_7165421 : Nat := 3679305064820114991084335

theorem tailTrace_7165421 : CollatzResearch.WordTrace tailWord_7165421 prefixEnd_7165421 3679305064820114991084335 := by
  unfold tailWord_7165421
  simp only [CollatzResearch.WordTrace]
  refine ⟨261344374173910948323680117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174229582782607298882453411 261344374173910948323680117)
  ·
    refine ⟨24501035078804151405345011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261344374173910948323680117 24501035078804151405345011)
    ·
      refine ⟨36751552618206227108017517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24501035078804151405345011 36751552618206227108017517)
      ·
        refine ⟨13781832231827335165506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36751552618206227108017517 13781832231827335165506569)
        ·
          refine ⟨10336374173870501374129927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13781832231827335165506569 10336374173870501374129927)
          ·
            refine ⟨15504561260805752061194891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336374173870501374129927 15504561260805752061194891)
            ·
              refine ⟨23256841891208628091792337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15504561260805752061194891 23256841891208628091792337)
              ·
                refine ⟨17442631418406471068844253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23256841891208628091792337 17442631418406471068844253)
                ·
                  refine ⟨6540986781902426650816595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17442631418406471068844253 6540986781902426650816595)
                  ·
                    refine ⟨9811480172853639976224893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6540986781902426650816595 9811480172853639976224893)
                    ·
                      refine ⟨3679305064820114991084335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811480172853639976224893 3679305064820114991084335)
                      ·
                        rfl

theorem cell23_7165421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7165421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165421 prefixEnd_7165421 := by exact prefixLift 7165421
  have htrace : WordTrace (prefixWord ++ tailWord_7165421) baseStart_7165421 baseEnd_7165421 := by
    simpa [prefixWord, tailWord_7165421, baseEnd_7165421] using wordTrace_append hprefix tailTrace_7165421
  have hstable : (prefixWord ++ tailWord_7165421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165421).length < 2 ^ (prefixWord ++ tailWord_7165421).sum := by decide
  have hdescent : baseEnd_7165421 < baseStart_7165421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165441 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7165441 : Nat := 118140960795 + 7165441 * 2 ^ 59
def prefixEnd_7165441 : Nat := 4983230072969 + 3 ^ 40 * 7165441 * 2
def baseEnd_7165441 : Nat := 1226438444811068304278081

theorem tailTrace_7165441 : CollatzResearch.WordTrace tailWord_7165441 prefixEnd_7165441 1226438444811068304278081 := by
  unfold tailWord_7165441
  simp only [CollatzResearch.WordTrace]
  refine ⟨261345103633838491739408177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174230069089225661159605451 261345103633838491739408177)
  ·
    refine ⟨196008827725378868804556133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261345103633838491739408177 196008827725378868804556133)
    ·
      refine ⟨36751655198508537900854275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196008827725378868804556133 36751655198508537900854275)
      ·
        refine ⟨55127482797762806851281413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36751655198508537900854275 55127482797762806851281413)
        ·
          refine ⟨10336403024580526284615265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55127482797762806851281413 10336403024580526284615265)
          ·
            refine ⟨7752302268435394713461449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336403024580526284615265 7752302268435394713461449)
            ·
              refine ⟨5814226701326546035096087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752302268435394713461449 5814226701326546035096087)
              ·
                refine ⟨8721340051989819052644131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814226701326546035096087 8721340051989819052644131)
                ·
                  refine ⟨13082010077984728578966197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8721340051989819052644131 13082010077984728578966197)
                  ·
                    refine ⟨1226438444811068304278081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13082010077984728578966197 1226438444811068304278081)
                    ·
                      rfl

theorem cell23_7165441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7165441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165441 prefixEnd_7165441 := by exact prefixLift 7165441
  have htrace : WordTrace (prefixWord ++ tailWord_7165441) baseStart_7165441 baseEnd_7165441 := by
    simpa [prefixWord, tailWord_7165441, baseEnd_7165441] using wordTrace_append hprefix tailTrace_7165441
  have hstable : (prefixWord ++ tailWord_7165441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165441).length < 2 ^ (prefixWord ++ tailWord_7165441).sum := by decide
  have hdescent : baseEnd_7165441 < baseStart_7165441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165450 : List Nat := [3, 1, 2, 2, 2, 3, 10]
def baseStart_7165450 : Nat := 118140960795 + 7165450 * 2 ^ 59
def prefixEnd_7165450 : Nat := 4983230072969 + 3 ^ 40 * 7165450 * 2
def baseEnd_7165450 : Nat := 45423703157519696020021

theorem tailTrace_7165450 : CollatzResearch.WordTrace tailWord_7165450 prefixEnd_7165450 45423703157519696020021 := by
  unfold tailWord_7165450
  simp only [CollatzResearch.WordTrace]
  refine ⟨65336357972701471569121451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174230287927203924184323869 65336357972701471569121451)
  ·
    refine ⟨98004536959052207353682177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65336357972701471569121451 98004536959052207353682177)
    ·
      refine ⟨73503402719289155515261633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98004536959052207353682177 73503402719289155515261633)
      ·
        refine ⟨55127552039466866636446225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73503402719289155515261633 55127552039466866636446225)
        ·
          refine ⟨41345664029600149977334669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55127552039466866636446225 41345664029600149977334669)
          ·
            refine ⟨15504624011100056241500501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41345664029600149977334669 15504624011100056241500501)
            ·
              refine ⟨45423703157519696020021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15504624011100056241500501 45423703157519696020021)
              ·
                rfl

theorem cell23_7165450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 10].length) (baseStart_7165450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165450 prefixEnd_7165450 := by exact prefixLift 7165450
  have htrace : WordTrace (prefixWord ++ tailWord_7165450) baseStart_7165450 baseEnd_7165450 := by
    simpa [prefixWord, tailWord_7165450, baseEnd_7165450] using wordTrace_append hprefix tailTrace_7165450
  have hstable : (prefixWord ++ tailWord_7165450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165450).length < 2 ^ (prefixWord ++ tailWord_7165450).sum := by decide
  have hdescent : baseEnd_7165450 < baseStart_7165450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165454 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_7165454 : Nat := 118140960795 + 7165454 * 2 ^ 59
def prefixEnd_7165454 : Nat := 4983230072969 + 3 ^ 40 * 7165454 * 2
def baseEnd_7165454 : Nat := 1226440669893904453990561

theorem tailTrace_7165454 : CollatzResearch.WordTrace tailWord_7165454 prefixEnd_7165454 1226440669893904453990561 := by
  unfold tailWord_7165454
  simp only [CollatzResearch.WordTrace]
  refine ⟨32668197222848924369953927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174230385188527596639754277 32668197222848924369953927)
  ·
    refine ⟨49002295834273386554930891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32668197222848924369953927 49002295834273386554930891)
    ·
      refine ⟨73503443751410079832396337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49002295834273386554930891 73503443751410079832396337)
      ·
        refine ⟨55127582813557559874297253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73503443751410079832396337 55127582813557559874297253)
        ·
          refine ⟨10336421777542042476430735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55127582813557559874297253 10336421777542042476430735)
          ·
            refine ⟨15504632666313063714646103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336421777542042476430735 15504632666313063714646103)
            ·
              refine ⟨23256948999469595571969155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15504632666313063714646103 23256948999469595571969155)
              ·
                refine ⟨34885423499204393357953733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23256948999469595571969155 34885423499204393357953733)
                ·
                  refine ⟨6541016906100823754616325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34885423499204393357953733 6541016906100823754616325)
                  ·
                    refine ⟨1226440669893904453990561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541016906100823754616325 1226440669893904453990561)
                    ·
                      rfl

theorem cell23_7165454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_7165454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165454 prefixEnd_7165454 := by exact prefixLift 7165454
  have htrace : WordTrace (prefixWord ++ tailWord_7165454) baseStart_7165454 baseEnd_7165454 := by
    simpa [prefixWord, tailWord_7165454, baseEnd_7165454] using wordTrace_append hprefix tailTrace_7165454
  have hstable : (prefixWord ++ tailWord_7165454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165454).length < 2 ^ (prefixWord ++ tailWord_7165454).sum := by decide
  have hdescent : baseEnd_7165454 < baseStart_7165454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165461 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_7165461 : Nat := 118140960795 + 7165461 * 2 ^ 59
def prefixEnd_7165461 : Nat := 4983230072969 + 3 ^ 40 * 7165461 * 2
def baseEnd_7165461 : Nat := 3679325604046294834584151

theorem tailTrace_7165461 : CollatzResearch.WordTrace tailWord_7165461 prefixEnd_7165461 3679325604046294834584151 := by
  unfold tailWord_7165461
  simp only [CollatzResearch.WordTrace]
  refine ⟨261345833093766035155136237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174230555395844023436757491 261345833093766035155136237)
  ·
    refine ⟨98004687410162263183176089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261345833093766035155136237 98004687410162263183176089)
    ·
      refine ⟨73503515557621697387382067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98004687410162263183176089 73503515557621697387382067)
      ·
        refine ⟨110255273336432546081073101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73503515557621697387382067 110255273336432546081073101)
        ·
          refine ⟨41345727501162204780402413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110255273336432546081073101 41345727501162204780402413)
          ·
            refine ⟨15504647812935826792650905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41345727501162204780402413 15504647812935826792650905)
            ·
              refine ⟨11628485859701870094488179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504647812935826792650905 11628485859701870094488179)
              ·
                refine ⟨17442728789552805141732269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628485859701870094488179 17442728789552805141732269)
                ·
                  refine ⟨6541023296082301928149601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17442728789552805141732269 6541023296082301928149601)
                  ·
                    refine ⟨4905767472061726446112201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6541023296082301928149601 4905767472061726446112201)
                    ·
                      refine ⟨3679325604046294834584151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4905767472061726446112201 3679325604046294834584151)
                      ·
                        rfl

theorem cell23_7165461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_7165461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165461 prefixEnd_7165461 := by exact prefixLift 7165461
  have htrace : WordTrace (prefixWord ++ tailWord_7165461) baseStart_7165461 baseEnd_7165461 := by
    simpa [prefixWord, tailWord_7165461, baseEnd_7165461] using wordTrace_append hprefix tailTrace_7165461
  have hstable : (prefixWord ++ tailWord_7165461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165461).length < 2 ^ (prefixWord ++ tailWord_7165461).sum := by decide
  have hdescent : baseEnd_7165461 < baseStart_7165461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165520 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_7165520 : Nat := 118140960795 + 7165520 * 2 ^ 59
def prefixEnd_7165520 : Nat := 4983230072969 + 3 ^ 40 * 7165520 * 2
def baseEnd_7165520 : Nat := 3679355899404910103746379

theorem tailTrace_7165520 : CollatzResearch.WordTrace tailWord_7165520 prefixEnd_7165520 3679355899404910103746379 := by
  unfold tailWord_7165520
  simp only [CollatzResearch.WordTrace]
  refine ⟨130673992500276144115767007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174231990000368192154356009 130673992500276144115767007)
  ·
    refine ⟨196010988750414216173650511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130673992500276144115767007 196010988750414216173650511)
    ·
      refine ⟨294016483125621324260475767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196010988750414216173650511 294016483125621324260475767)
      ·
        refine ⟨441024724688431986390713651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294016483125621324260475767 441024724688431986390713651)
        ·
          refine ⟨661537087032647979586070477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441024724688431986390713651 661537087032647979586070477)
          ·
            refine ⟨248076407637242992344776429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661537087032647979586070477 248076407637242992344776429)
            ·
              refine ⟨93028652863966122129291161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248076407637242992344776429 93028652863966122129291161)
              ·
                refine ⟨69771489647974591596968371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93028652863966122129291161 69771489647974591596968371)
                ·
                  refine ⟨104657234471961887395452557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69771489647974591596968371 104657234471961887395452557)
                  ·
                    refine ⟨39246462926985707773294709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104657234471961887395452557 39246462926985707773294709)
                    ·
                      refine ⟨3679355899404910103746379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39246462926985707773294709 3679355899404910103746379)
                      ·
                        rfl

theorem cell23_7165520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_7165520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165520 prefixEnd_7165520 := by exact prefixLift 7165520
  have htrace : WordTrace (prefixWord ++ tailWord_7165520) baseStart_7165520 baseEnd_7165520 := by
    simpa [prefixWord, tailWord_7165520, baseEnd_7165520] using wordTrace_append hprefix tailTrace_7165520
  have hstable : (prefixWord ++ tailWord_7165520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165520).length < 2 ^ (prefixWord ++ tailWord_7165520).sum := by decide
  have hdescent : baseEnd_7165520 < baseStart_7165520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165530 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_7165530 : Nat := 118140960795 + 7165530 * 2 ^ 59
def prefixEnd_7165530 : Nat := 4983230072969 + 3 ^ 40 * 7165530 * 2
def baseEnd_7165530 : Nat := 3679361034211455064621333

theorem tailTrace_7165530 : CollatzResearch.WordTrace tailWord_7165530 prefixEnd_7165530 3679361034211455064621333 := by
  unfold tailWord_7165530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65337087432629014984849511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174232233153677373292932029 65337087432629014984849511)
  ·
    refine ⟨98005631148943522477274267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65337087432629014984849511 98005631148943522477274267)
    ·
      refine ⟨147008446723415283715911401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98005631148943522477274267 147008446723415283715911401)
      ·
        refine ⟨110256335042561462786933551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147008446723415283715911401 110256335042561462786933551)
        ·
          refine ⟨165384502563842194180400327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110256335042561462786933551 165384502563842194180400327)
          ·
            refine ⟨248076753845763291270600491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165384502563842194180400327 248076753845763291270600491)
            ·
              refine ⟨372115130768644936905900737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248076753845763291270600491 372115130768644936905900737)
              ·
                refine ⟨279086348076483702679425553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372115130768644936905900737 279086348076483702679425553)
                ·
                  refine ⟨209314761057362777009569165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279086348076483702679425553 209314761057362777009569165)
                  ·
                    refine ⟨78493035396511041378588437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209314761057362777009569165 78493035396511041378588437)
                    ·
                      refine ⟨3679361034211455064621333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78493035396511041378588437 3679361034211455064621333)
                      ·
                        rfl

theorem cell23_7165530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_7165530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165530 prefixEnd_7165530 := by exact prefixLift 7165530
  have htrace : WordTrace (prefixWord ++ tailWord_7165530) baseStart_7165530 baseEnd_7165530 := by
    simpa [prefixWord, tailWord_7165530, baseEnd_7165530] using wordTrace_append hprefix tailTrace_7165530
  have hstable : (prefixWord ++ tailWord_7165530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165530).length < 2 ^ (prefixWord ++ tailWord_7165530).sum := by decide
  have hdescent : baseEnd_7165530 < baseStart_7165530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165560 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_7165560 : Nat := 118140960795 + 7165560 * 2 ^ 59
def prefixEnd_7165560 : Nat := 4983230072969 + 3 ^ 40 * 7165560 * 2
def baseEnd_7165560 : Nat := 3679376438631089947246195

theorem tailTrace_7165560 : CollatzResearch.WordTrace tailWord_7165560 prefixEnd_7165560 3679376438631089947246195 := by
  unfold tailWord_7165560
  simp only [CollatzResearch.WordTrace]
  refine ⟨130674721960203687531495067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174232962613604916708660089 130674721960203687531495067)
  ·
    refine ⟨196012082940305531297242601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130674721960203687531495067 196012082940305531297242601)
    ·
      refine ⟨147009062205229148472931951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196012082940305531297242601 147009062205229148472931951)
      ·
        refine ⟨220513593307843722709397927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147009062205229148472931951 220513593307843722709397927)
        ·
          refine ⟨330770389961765584064096891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220513593307843722709397927 330770389961765584064096891)
          ·
            refine ⟨496155584942648376096145337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330770389961765584064096891 496155584942648376096145337)
            ·
              refine ⟨372116688706986282072109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496155584942648376096145337 372116688706986282072109003)
              ·
                refine ⟨558175033060479423108163505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372116688706986282072109003 558175033060479423108163505)
                ·
                  refine ⟨418631274795359567331122629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558175033060479423108163505 418631274795359567331122629)
                  ·
                    refine ⟨78493364024129918874585493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418631274795359567331122629 78493364024129918874585493)
                    ·
                      refine ⟨3679376438631089947246195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78493364024129918874585493 3679376438631089947246195)
                      ·
                        rfl

theorem cell23_7165560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_7165560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165560 prefixEnd_7165560 := by exact prefixLift 7165560
  have htrace : WordTrace (prefixWord ++ tailWord_7165560) baseStart_7165560 baseEnd_7165560 := by
    simpa [prefixWord, tailWord_7165560, baseEnd_7165560] using wordTrace_append hprefix tailTrace_7165560
  have hstable : (prefixWord ++ tailWord_7165560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165560).length < 2 ^ (prefixWord ++ tailWord_7165560).sum := by decide
  have hdescent : baseEnd_7165560 < baseStart_7165560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165604 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_7165604 : Nat := 118140960795 + 7165604 * 2 ^ 59
def prefixEnd_7165604 : Nat := 4983230072969 + 3 ^ 40 * 7165604 * 2
def baseEnd_7165604 : Nat := 1226466343926629258365331

theorem tailTrace_7165604 : CollatzResearch.WordTrace tailWord_7165604 prefixEnd_7165604 1226466343926629258365331 := by
  unfold tailWord_7165604
  simp only [CollatzResearch.WordTrace]
  refine ⟨130675524366123985288795933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174234032488165313718394577 130675524366123985288795933)
  ·
    refine ⟨49003321637296494483298475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130675524366123985288795933 49003321637296494483298475)
    ·
      refine ⟨73504982455944741724947713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49003321637296494483298475 73504982455944741724947713)
      ·
        refine ⟨55128736841958556293710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73504982455944741724947713 55128736841958556293710785)
        ·
          refine ⟨41346552631468917220283089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55128736841958556293710785 41346552631468917220283089)
          ·
            refine ⟨31009914473601687915212317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41346552631468917220283089 31009914473601687915212317)
            ·
              refine ⟨11628717927600632968204619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31009914473601687915212317 11628717927600632968204619)
              ·
                refine ⟨17443076891400949452306929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628717927600632968204619 17443076891400949452306929)
                ·
                  refine ⟨13082307668550712089230197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17443076891400949452306929 13082307668550712089230197)
                  ·
                    refine ⟨1226466343926629258365331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13082307668550712089230197 1226466343926629258365331)
                    ·
                      rfl

theorem cell23_7165604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_7165604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165604 prefixEnd_7165604 := by exact prefixLift 7165604
  have htrace : WordTrace (prefixWord ++ tailWord_7165604) baseStart_7165604 baseEnd_7165604 := by
    simpa [prefixWord, tailWord_7165604, baseEnd_7165604] using wordTrace_append hprefix tailTrace_7165604
  have hstable : (prefixWord ++ tailWord_7165604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165604).length < 2 ^ (prefixWord ++ tailWord_7165604).sum := by decide
  have hdescent : baseEnd_7165604 < baseStart_7165604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165647 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 6]
def baseStart_7165647 : Nat := 118140960795 + 7165647 * 2 ^ 59
def prefixEnd_7165647 : Nat := 4983230072969 + 3 ^ 40 * 7165647 * 2
def baseEnd_7165647 : Nat := 408824567938670122984255

theorem tailTrace_7165647 : CollatzResearch.WordTrace tailWord_7165647 prefixEnd_7165647 408824567938670122984255 := by
  unfold tailWord_7165647
  simp only [CollatzResearch.WordTrace]
  refine ⟨261352617071092188921407195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174235078047394792614271463 261352617071092188921407195)
  ·
    refine ⟨392028925606638283382110793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261352617071092188921407195 392028925606638283382110793)
    ·
      refine ⟨294021694204978712536583095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392028925606638283382110793 294021694204978712536583095)
      ·
        refine ⟨441032541307468068804874643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294021694204978712536583095 441032541307468068804874643)
        ·
          refine ⟨661548811961202103207311965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441032541307468068804874643 661548811961202103207311965)
          ·
            refine ⟨248080804485450788702741987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661548811961202103207311965 248080804485450788702741987)
            ·
              refine ⟨372121206728176183054112981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248080804485450788702741987 372121206728176183054112981)
              ·
                refine ⟨8721590782691629290330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 372121206728176183054112981 8721590782691629290330773)
                ·
                  refine ⟨408824567938670122984255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8721590782691629290330773 408824567938670122984255)
                  ·
                    rfl

theorem cell23_7165647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 6].length) (baseStart_7165647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165647 prefixEnd_7165647 := by exact prefixLift 7165647
  have htrace : WordTrace (prefixWord ++ tailWord_7165647) baseStart_7165647 baseEnd_7165647 := by
    simpa [prefixWord, tailWord_7165647, baseEnd_7165647] using wordTrace_append hprefix tailTrace_7165647
  have hstable : (prefixWord ++ tailWord_7165647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165647).length < 2 ^ (prefixWord ++ tailWord_7165647).sum := by decide
  have hdescent : baseEnd_7165647 < baseStart_7165647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165724 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_7165724 : Nat := 118140960795 + 7165724 * 2 ^ 59
def prefixEnd_7165724 : Nat := 4983230072969 + 3 ^ 40 * 7165724 * 2
def baseEnd_7165724 : Nat := 1226486883152809101865147

theorem tailTrace_7165724 : CollatzResearch.WordTrace tailWord_7165724 prefixEnd_7165724 1226486883152809101865147 := by
  unfold tailWord_7165724
  simp only [CollatzResearch.WordTrace]
  refine ⟨130677712745906615535980113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174236950327875487381306817 130677712745906615535980113)
  ·
    refine ⟨98008284559429961651985085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130677712745906615535980113 98008284559429961651985085)
    ·
      refine ⟨36753106709786235619494407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98008284559429961651985085 36753106709786235619494407)
      ·
        refine ⟨55129660064679353429241611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36753106709786235619494407 55129660064679353429241611)
        ·
          refine ⟨82694490097019030143862417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55129660064679353429241611 82694490097019030143862417)
          ·
            refine ⟨62020867572764272607896813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82694490097019030143862417 62020867572764272607896813)
            ·
              refine ⟨23257825339786602227961305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62020867572764272607896813 23257825339786602227961305)
              ·
                refine ⟨17443369004839951670970979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23257825339786602227961305 17443369004839951670970979)
                ·
                  refine ⟨26165053507259927506456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17443369004839951670970979 26165053507259927506456469)
                  ·
                    refine ⟨1226486883152809101865147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26165053507259927506456469 1226486883152809101865147)
                    ·
                      rfl

theorem cell23_7165724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_7165724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165724 prefixEnd_7165724 := by exact prefixLift 7165724
  have htrace : WordTrace (prefixWord ++ tailWord_7165724) baseStart_7165724 baseEnd_7165724 := by
    simpa [prefixWord, tailWord_7165724, baseEnd_7165724] using wordTrace_append hprefix tailTrace_7165724
  have hstable : (prefixWord ++ tailWord_7165724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165724).length < 2 ^ (prefixWord ++ tailWord_7165724).sum := by decide
  have hdescent : baseEnd_7165724 < baseStart_7165724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165742 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7165742 : Nat := 118140960795 + 7165742 * 2 ^ 59
def prefixEnd_7165742 : Nat := 4983230072969 + 3 ^ 40 * 7165742 * 2
def baseEnd_7165742 : Nat := 3679469892110208235170359

theorem tailTrace_7165742 : CollatzResearch.WordTrace tailWord_7165742 prefixEnd_7165742 3679469892110208235170359 := by
  unfold tailWord_7165742
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669510250718502518264435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174237388003832013430743653 32669510250718502518264435)
  ·
    refine ⟨49004265376077753777396653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32669510250718502518264435 49004265376077753777396653)
    ·
      refine ⟨18376599516029157666523745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49004265376077753777396653 18376599516029157666523745)
      ·
        refine ⟨13782449637021868249892809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18376599516029157666523745 13782449637021868249892809)
        ·
          refine ⟨10336837227766401187419607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13782449637021868249892809 10336837227766401187419607)
          ·
            refine ⟨15505255841649601781129411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336837227766401187419607 15505255841649601781129411)
            ·
              refine ⟨23257883762474402671694117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15505255841649601781129411 23257883762474402671694117)
              ·
                refine ⟨4360853205463950500942647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23257883762474402671694117 4360853205463950500942647)
                ·
                  refine ⟨6541279808195925751413971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360853205463950500942647 6541279808195925751413971)
                  ·
                    refine ⟨9811919712293888627120957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6541279808195925751413971 9811919712293888627120957)
                    ·
                      refine ⟨3679469892110208235170359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811919712293888627120957 3679469892110208235170359)
                      ·
                        rfl

theorem cell23_7165742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7165742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165742 prefixEnd_7165742 := by exact prefixLift 7165742
  have htrace : WordTrace (prefixWord ++ tailWord_7165742) baseStart_7165742 baseEnd_7165742 := by
    simpa [prefixWord, tailWord_7165742, baseEnd_7165742] using wordTrace_append hprefix tailTrace_7165742
  have hstable : (prefixWord ++ tailWord_7165742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165742).length < 2 ^ (prefixWord ++ tailWord_7165742).sum := by decide
  have hdescent : baseEnd_7165742 < baseStart_7165742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165754 : List Nat := [3, 1, 1, 1, 5, 1, 3, 8]
def baseStart_7165754 : Nat := 118140960795 + 7165754 * 2 ^ 59
def prefixEnd_7165754 : Nat := 4983230072969 + 3 ^ 40 * 7165754 * 2
def baseEnd_7165754 : Nat := 136276890884372673637789

theorem tailTrace_7165754 : CollatzResearch.WordTrace tailWord_7165754 prefixEnd_7165754 136276890884372673637789 := by
  unfold tailWord_7165754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65339129920426136548888079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174237679787803030797034877 65339129920426136548888079)
  ·
    refine ⟨98008694880639204823332119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65339129920426136548888079 98008694880639204823332119)
    ·
      refine ⟨147013042320958807234998179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98008694880639204823332119 147013042320958807234998179)
      ·
        refine ⟨220519563481438210852497269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147013042320958807234998179 220519563481438210852497269)
        ·
          refine ⟨20673709076384832267421619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220519563481438210852497269 20673709076384832267421619)
          ·
            refine ⟨31010563614577248401132429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20673709076384832267421619 31010563614577248401132429)
            ·
              refine ⟨11628961355466468150424661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31010563614577248401132429 11628961355466468150424661)
              ·
                refine ⟨136276890884372673637789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11628961355466468150424661 136276890884372673637789)
                ·
                  rfl

theorem cell23_7165754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_7165754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165754 prefixEnd_7165754 := by exact prefixLift 7165754
  have htrace : WordTrace (prefixWord ++ tailWord_7165754) baseStart_7165754 baseEnd_7165754 := by
    simpa [prefixWord, tailWord_7165754, baseEnd_7165754] using wordTrace_append hprefix tailTrace_7165754
  have hstable : (prefixWord ++ tailWord_7165754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165754).length < 2 ^ (prefixWord ++ tailWord_7165754).sum := by decide
  have hdescent : baseEnd_7165754 < baseStart_7165754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165758 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_7165758 : Nat := 118140960795 + 7165758 * 2 ^ 59
def prefixEnd_7165758 : Nat := 4983230072969 + 3 ^ 40 * 7165758 * 2
def baseEnd_7165758 : Nat := 1226492702600226724190095

theorem tailTrace_7165758 : CollatzResearch.WordTrace tailWord_7165758 prefixEnd_7165758 1226492702600226724190095 := by
  unfold tailWord_7165758
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669583196711256859837241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174237777049126703252465285 32669583196711256859837241)
  ·
    refine ⟨24502187397533442644877931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32669583196711256859837241 24502187397533442644877931)
    ·
      refine ⟨36753281096300163967316897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24502187397533442644877931 36753281096300163967316897)
      ·
        refine ⟨27564960822225122975487673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36753281096300163967316897 27564960822225122975487673)
        ·
          refine ⟨20673720616668842231615755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27564960822225122975487673 20673720616668842231615755)
          ·
            refine ⟨31010580925003263347423633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20673720616668842231615755 31010580925003263347423633)
            ·
              refine ⟨23257935693752447510567725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31010580925003263347423633 23257935693752447510567725)
              ·
                refine ⟨8721725885157167816462897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23257935693752447510567725 8721725885157167816462897)
                ·
                  refine ⟨6541294413867875862347173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8721725885157167816462897 6541294413867875862347173)
                  ·
                    refine ⟨1226492702600226724190095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541294413867875862347173 1226492702600226724190095)
                    ·
                      rfl

theorem cell23_7165758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_7165758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165758 prefixEnd_7165758 := by exact prefixLift 7165758
  have htrace : WordTrace (prefixWord ++ tailWord_7165758) baseStart_7165758 baseEnd_7165758 := by
    simpa [prefixWord, tailWord_7165758, baseEnd_7165758] using wordTrace_append hprefix tailTrace_7165758
  have hstable : (prefixWord ++ tailWord_7165758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165758).length < 2 ^ (prefixWord ++ tailWord_7165758).sum := by decide
  have hdescent : baseEnd_7165758 < baseStart_7165758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165781 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7165781 : Nat := 118140960795 + 7165781 * 2 ^ 59
def prefixEnd_7165781 : Nat := 4983230072969 + 3 ^ 40 * 7165781 * 2
def baseEnd_7165781 : Nat := 3679489917855733582582679

theorem tailTrace_7165781 : CollatzResearch.WordTrace tailWord_7165781 prefixEnd_7165781 3679489917855733582582679 := by
  unfold tailWord_7165781
  simp only [CollatzResearch.WordTrace]
  refine ⟨261357504452606729806785197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174238336301737819871190131 261357504452606729806785197)
  ·
    refine ⟨98009064169727523677544449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261357504452606729806785197 98009064169727523677544449)
    ·
      refine ⟨73506798127295642758158337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98009064169727523677544449 73506798127295642758158337)
      ·
        refine ⟨55130098595471732068618753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73506798127295642758158337 55130098595471732068618753)
        ·
          refine ⟨41347573946603799051464065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55130098595471732068618753 41347573946603799051464065)
          ·
            refine ⟨31010680459952849288598049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41347573946603799051464065 31010680459952849288598049)
            ·
              refine ⟨23258010344964636966448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31010680459952849288598049 23258010344964636966448537)
              ·
                refine ⟨17443507758723477724836403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23258010344964636966448537 17443507758723477724836403)
                ·
                  refine ⟨26165261638085216587254605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17443507758723477724836403 26165261638085216587254605)
                  ·
                    refine ⟨9811973114281956220220477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26165261638085216587254605 9811973114281956220220477)
                    ·
                      refine ⟨3679489917855733582582679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9811973114281956220220477 3679489917855733582582679)
                      ·
                        rfl

theorem cell23_7165781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7165781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165781 prefixEnd_7165781 := by exact prefixLift 7165781
  have htrace : WordTrace (prefixWord ++ tailWord_7165781) baseStart_7165781 baseEnd_7165781 := by
    simpa [prefixWord, tailWord_7165781, baseEnd_7165781] using wordTrace_append hprefix tailTrace_7165781
  have hstable : (prefixWord ++ tailWord_7165781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165781).length < 2 ^ (prefixWord ++ tailWord_7165781).sum := by decide
  have hdescent : baseEnd_7165781 < baseStart_7165781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165824 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_7165824 : Nat := 118140960795 + 7165824 * 2 ^ 59
def prefixEnd_7165824 : Nat := 4983230072969 + 3 ^ 40 * 7165824 * 2
def baseEnd_7165824 : Nat := 3679511997523876914344981

theorem tailTrace_7165824 : CollatzResearch.WordTrace tailWord_7165824 prefixEnd_7165824 3679511997523876914344981 := by
  unfold tailWord_7165824
  simp only [CollatzResearch.WordTrace]
  refine ⟨130679536395725474075300263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174239381860967298767067017 130679536395725474075300263)
  ·
    refine ⟨196019304593588211112950395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130679536395725474075300263 196019304593588211112950395)
    ·
      refine ⟨294028956890382316669425593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196019304593588211112950395 294028956890382316669425593)
      ·
        refine ⟨220521717667786737502069195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294028956890382316669425593 220521717667786737502069195)
        ·
          refine ⟨330782576501680106253103793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220521717667786737502069195 330782576501680106253103793)
          ·
            refine ⟨248086932376260079689827845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330782576501680106253103793 248086932376260079689827845)
            ·
              refine ⟨46516299820548764941842721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248086932376260079689827845 46516299820548764941842721)
              ·
                refine ⟨34887224865411573706382041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46516299820548764941842721 34887224865411573706382041)
                ·
                  refine ⟨26165418649058680279786531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34887224865411573706382041 26165418649058680279786531)
                  ·
                    refine ⟨39248127973588020419679797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26165418649058680279786531 39248127973588020419679797)
                    ·
                      refine ⟨3679511997523876914344981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39248127973588020419679797 3679511997523876914344981)
                      ·
                        rfl

theorem cell23_7165824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_7165824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165824 prefixEnd_7165824 := by exact prefixLift 7165824
  have htrace : WordTrace (prefixWord ++ tailWord_7165824) baseStart_7165824 baseEnd_7165824 := by
    simpa [prefixWord, tailWord_7165824, baseEnd_7165824] using wordTrace_append hprefix tailTrace_7165824
  have hstable : (prefixWord ++ tailWord_7165824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165824).length < 2 ^ (prefixWord ++ tailWord_7165824).sum := by decide
  have hdescent : baseEnd_7165824 < baseStart_7165824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165861 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 5]
def baseStart_7165861 : Nat := 118140960795 + 7165861 * 2 ^ 59
def prefixEnd_7165861 : Nat := 4983230072969 + 3 ^ 40 * 7165861 * 2
def baseEnd_7165861 : Nat := 408836777367565918842479

theorem tailTrace_7165861 : CollatzResearch.WordTrace tailWord_7165861 prefixEnd_7165861 408836777367565918842479 := by
  unfold tailWord_7165861
  simp only [CollatzResearch.WordTrace]
  refine ⟨261360422292316903469697437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174240281528211268979798291 261360422292316903469697437)
  ·
    refine ⟨98010158359618838801136539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261360422292316903469697437 98010158359618838801136539)
    ·
      refine ⟨147015237539428258201704809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98010158359618838801136539 147015237539428258201704809)
      ·
        refine ⟨110261428154571193651278607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147015237539428258201704809 110261428154571193651278607)
        ·
          refine ⟨165392142231856790476917911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110261428154571193651278607 165392142231856790476917911)
          ·
            refine ⟨248088213347785185715376867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165392142231856790476917911 248088213347785185715376867)
            ·
              refine ⟨372132320021677778573065301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248088213347785185715376867 372132320021677778573065301)
              ·
                refine ⟨4360925625254036467653109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 372132320021677778573065301 4360925625254036467653109)
                ·
                  refine ⟨408836777367565918842479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4360925625254036467653109 408836777367565918842479)
                  ·
                    rfl

theorem cell23_7165861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_7165861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165861 prefixEnd_7165861 := by exact prefixLift 7165861
  have htrace : WordTrace (prefixWord ++ tailWord_7165861) baseStart_7165861 baseEnd_7165861 := by
    simpa [prefixWord, tailWord_7165861, baseEnd_7165861] using wordTrace_append hprefix tailTrace_7165861
  have hstable : (prefixWord ++ tailWord_7165861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165861).length < 2 ^ (prefixWord ++ tailWord_7165861).sum := by decide
  have hdescent : baseEnd_7165861 < baseStart_7165861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165874 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_7165874 : Nat := 118140960795 + 7165874 * 2 ^ 59
def prefixEnd_7165874 : Nat := 4983230072969 + 3 ^ 40 * 7165874 * 2
def baseEnd_7165874 : Nat := 1226512557185533906239917

theorem tailTrace_7165874 : CollatzResearch.WordTrace tailWord_7165874 prefixEnd_7165874 1226512557185533906239917 := by
  unfold tailWord_7165874
  simp only [CollatzResearch.WordTrace]
  refine ⟨65340224110317451672480169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174240597627513204459947117 65340224110317451672480169)
  ·
    refine ⟨49005168082738088754360127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65340224110317451672480169 49005168082738088754360127)
    ·
      refine ⟨73507752124107133131540191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49005168082738088754360127 73507752124107133131540191)
      ·
        refine ⟨110261628186160699697310287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73507752124107133131540191 110261628186160699697310287)
        ·
          refine ⟨165392442279241049545965431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110261628186160699697310287 165392442279241049545965431)
          ·
            refine ⟨248088663418861574318948147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165392442279241049545965431 248088663418861574318948147)
            ·
              refine ⟨372132995128292361478422221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248088663418861574318948147 372132995128292361478422221)
              ·
                refine ⟨139549873173109635554408333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372132995128292361478422221 139549873173109635554408333)
                ·
                  refine ⟨52331202439916113332903125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139549873173109635554408333 52331202439916113332903125)
                  ·
                    refine ⟨1226512557185533906239917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52331202439916113332903125 1226512557185533906239917)
                    ·
                      rfl

theorem cell23_7165874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_7165874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165874 prefixEnd_7165874 := by exact prefixLift 7165874
  have htrace : WordTrace (prefixWord ++ tailWord_7165874) baseStart_7165874 baseEnd_7165874 := by
    simpa [prefixWord, tailWord_7165874, baseEnd_7165874] using wordTrace_append hprefix tailTrace_7165874
  have hstable : (prefixWord ++ tailWord_7165874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165874).length < 2 ^ (prefixWord ++ tailWord_7165874).sum := by decide
  have hdescent : baseEnd_7165874 < baseStart_7165874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165876 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7165876 : Nat := 118140960795 + 7165876 * 2 ^ 59
def prefixEnd_7165876 : Nat := 4983230072969 + 3 ^ 40 * 7165876 * 2
def baseEnd_7165876 : Nat := 3679538698517910710894743

theorem tailTrace_7165876 : CollatzResearch.WordTrace tailWord_7165876 prefixEnd_7165876 3679538698517910710894743 := by
  unfold tailWord_7165876
  simp only [CollatzResearch.WordTrace]
  refine ⟨130680484693631280515746741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174240646258175040687662321 130680484693631280515746741)
  ·
    refine ⟨12251295440027932548351257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130680484693631280515746741 12251295440027932548351257)
    ·
      refine ⟨9188471580020949411263443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12251295440027932548351257 9188471580020949411263443)
      ·
        refine ⟨13782707370031424116895165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188471580020949411263443 13782707370031424116895165)
        ·
          refine ⟨5168515263761784043835687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13782707370031424116895165 5168515263761784043835687)
          ·
            refine ⟨7752772895642676065753531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168515263761784043835687 7752772895642676065753531)
            ·
              refine ⟨11629159343464014098630297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752772895642676065753531 11629159343464014098630297)
              ·
                refine ⟨8721869507598010573972723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629159343464014098630297 8721869507598010573972723)
                ·
                  refine ⟨13082804261397015860959085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8721869507598010573972723 13082804261397015860959085)
                  ·
                    refine ⟨4906051598023880947859657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13082804261397015860959085 4906051598023880947859657)
                    ·
                      refine ⟨3679538698517910710894743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906051598023880947859657 3679538698517910710894743)
                      ·
                        rfl

theorem cell23_7165876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7165876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165876 prefixEnd_7165876 := by exact prefixLift 7165876
  have htrace : WordTrace (prefixWord ++ tailWord_7165876) baseStart_7165876 baseEnd_7165876 := by
    simpa [prefixWord, tailWord_7165876, baseEnd_7165876] using wordTrace_append hprefix tailTrace_7165876
  have hstable : (prefixWord ++ tailWord_7165876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165876).length < 2 ^ (prefixWord ++ tailWord_7165876).sum := by decide
  have hdescent : baseEnd_7165876 < baseStart_7165876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165911 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_7165911 : Nat := 118140960795 + 7165911 * 2 ^ 59
def prefixEnd_7165911 : Nat := 4983230072969 + 3 ^ 40 * 7165911 * 2
def baseEnd_7165911 : Nat := 3679556670340818073957081

theorem tailTrace_7165911 : CollatzResearch.WordTrace tailWord_7165911 prefixEnd_7165911 3679556670340818073957081 := by
  unfold tailWord_7165911
  simp only [CollatzResearch.WordTrace]
  refine ⟨261362245942135762009017587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174241497294757174672678391 261362245942135762009017587)
  ·
    refine ⟨392043368913203643013526381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261362245942135762009017587 392043368913203643013526381)
    ·
      refine ⟨147016263342451366130072393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392043368913203643013526381 147016263342451366130072393)
      ·
        refine ⟨110262197506838524597554295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147016263342451366130072393 110262197506838524597554295)
        ·
          refine ⟨165393296260257786896331443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110262197506838524597554295 165393296260257786896331443)
          ·
            refine ⟨248089944390386680344497165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165393296260257786896331443 248089944390386680344497165)
            ·
              refine ⟨93033729146395005129186437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248089944390386680344497165 93033729146395005129186437)
              ·
                refine ⟨17443824214949063461722457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93033729146395005129186437 17443824214949063461722457)
                ·
                  refine ⟨13082868161211797596291843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17443824214949063461722457 13082868161211797596291843)
                  ·
                    refine ⟨19624302241817696394437765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13082868161211797596291843 19624302241817696394437765)
                    ·
                      refine ⟨3679556670340818073957081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19624302241817696394437765 3679556670340818073957081)
                      ·
                        rfl

theorem cell23_7165911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_7165911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165911 prefixEnd_7165911 := by exact prefixLift 7165911
  have htrace : WordTrace (prefixWord ++ tailWord_7165911) baseStart_7165911 baseEnd_7165911 := by
    simpa [prefixWord, tailWord_7165911, baseEnd_7165911] using wordTrace_append hprefix tailTrace_7165911
  have hstable : (prefixWord ++ tailWord_7165911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165911).length < 2 ^ (prefixWord ++ tailWord_7165911).sum := by decide
  have hdescent : baseEnd_7165911 < baseStart_7165911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165931 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3]
def baseStart_7165931 : Nat := 118140960795 + 7165931 * 2 ^ 59
def prefixEnd_7165931 : Nat := 4983230072969 + 3 ^ 40 * 7165931 * 2
def baseEnd_7165931 : Nat := 3679566939953907995706989

theorem tailTrace_7165931 : CollatzResearch.WordTrace tailWord_7165931 prefixEnd_7165931 3679566939953907995706989 := by
  unfold tailWord_7165931
  simp only [CollatzResearch.WordTrace]
  refine ⟨261362975402063305424745647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174241983601375536949830431 261362975402063305424745647)
  ·
    refine ⟨392044463103094958137118471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261362975402063305424745647 392044463103094958137118471)
    ·
      refine ⟨588066694654642437205677707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392044463103094958137118471 588066694654642437205677707)
      ·
        refine ⟨882100041981963655808516561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588066694654642437205677707 882100041981963655808516561)
        ·
          refine ⟨661575031486472741856387421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882100041981963655808516561 661575031486472741856387421)
          ·
            refine ⟨248090636807427278196145283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661575031486472741856387421 248090636807427278196145283)
            ·
              refine ⟨372135955211140917294217925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248090636807427278196145283 372135955211140917294217925)
              ·
                refine ⟨69775491602088921992665861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372135955211140917294217925 69775491602088921992665861)
                ·
                  refine ⟨13082904675391672873624849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69775491602088921992665861 13082904675391672873624849)
                  ·
                    refine ⟨9812178506543754655218637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13082904675391672873624849 9812178506543754655218637)
                    ·
                      refine ⟨3679566939953907995706989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9812178506543754655218637 3679566939953907995706989)
                      ·
                        rfl

theorem cell23_7165931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].length) (baseStart_7165931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165931 prefixEnd_7165931 := by exact prefixLift 7165931
  have htrace : WordTrace (prefixWord ++ tailWord_7165931) baseStart_7165931 baseEnd_7165931 := by
    simpa [prefixWord, tailWord_7165931, baseEnd_7165931] using wordTrace_append hprefix tailTrace_7165931
  have hstable : (prefixWord ++ tailWord_7165931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165931).length < 2 ^ (prefixWord ++ tailWord_7165931).sum := by decide
  have hdescent : baseEnd_7165931 < baseStart_7165931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165942 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_7165942 : Nat := 118140960795 + 7165942 * 2 ^ 59
def prefixEnd_7165942 : Nat := 4983230072969 + 3 ^ 40 * 7165942 * 2
def baseEnd_7165942 : Nat := 1226524196080369150889813

theorem tailTrace_7165942 : CollatzResearch.WordTrace tailWord_7165942 prefixEnd_7165942 1226524196080369150889813 := by
  unfold tailWord_7165942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335211037813965893962255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174242251070015636202264053 16335211037813965893962255)
  ·
    refine ⟨24502816556720948840943383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335211037813965893962255 24502816556720948840943383)
    ·
      refine ⟨36754224835081423261415075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24502816556720948840943383 36754224835081423261415075)
      ·
        refine ⟨55131337252622134892122613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36754224835081423261415075 55131337252622134892122613)
        ·
          refine ⟨5168562867433325146136495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55131337252622134892122613 5168562867433325146136495)
          ·
            refine ⟨7752844301149987719204743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168562867433325146136495 7752844301149987719204743)
            ·
              refine ⟨11629266451724981578807115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752844301149987719204743 11629266451724981578807115)
              ·
                refine ⟨17443899677587472368210673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11629266451724981578807115 17443899677587472368210673)
                ·
                  refine ⟨13082924758190604276158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17443899677587472368210673 13082924758190604276158005)
                  ·
                    refine ⟨1226524196080369150889813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13082924758190604276158005 1226524196080369150889813)
                    ·
                      rfl

theorem cell23_7165942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_7165942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165942 prefixEnd_7165942 := by exact prefixLift 7165942
  have htrace : WordTrace (prefixWord ++ tailWord_7165942) baseStart_7165942 baseEnd_7165942 := by
    simpa [prefixWord, tailWord_7165942, baseEnd_7165942] using wordTrace_append hprefix tailTrace_7165942
  have hstable : (prefixWord ++ tailWord_7165942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165942).length < 2 ^ (prefixWord ++ tailWord_7165942).sum := by decide
  have hdescent : baseEnd_7165942 < baseStart_7165942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7165985 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 6]
def baseStart_7165985 : Nat := 118140960795 + 7165985 * 2 ^ 59
def prefixEnd_7165985 : Nat := 4983230072969 + 3 ^ 40 * 7165985 * 2
def baseEnd_7165985 : Nat := 408843851989916753825749

theorem tailTrace_7165985 : CollatzResearch.WordTrace tailWord_7165985 prefixEnd_7165985 408843851989916753825749 := by
  unfold tailWord_7165985
  simp only [CollatzResearch.WordTrace]
  refine ⟨261364944943867672647211409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174243296629245115098140939 261364944943867672647211409)
  ·
    refine ⟨196023708707900754485408557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261364944943867672647211409 196023708707900754485408557)
    ·
      refine ⟨73508890765462782932028209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196023708707900754485408557 73508890765462782932028209)
      ·
        refine ⟨55131668074097087199021157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73508890765462782932028209 55131668074097087199021157)
        ·
          refine ⟨10337187763893203849816467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55131668074097087199021157 10337187763893203849816467)
          ·
            refine ⟨15505781645839805774724701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337187763893203849816467 15505781645839805774724701)
            ·
              refine ⟨5814668117189927165521763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15505781645839805774724701 5814668117189927165521763)
              ·
                refine ⟨8722002175784890748282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814668117189927165521763 8722002175784890748282645)
                ·
                  refine ⟨408843851989916753825749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8722002175784890748282645 408843851989916753825749)
                  ·
                    rfl

theorem cell23_7165985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_7165985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7165985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7165985 prefixEnd_7165985 := by exact prefixLift 7165985
  have htrace : WordTrace (prefixWord ++ tailWord_7165985) baseStart_7165985 baseEnd_7165985 := by
    simpa [prefixWord, tailWord_7165985, baseEnd_7165985] using wordTrace_append hprefix tailTrace_7165985
  have hstable : (prefixWord ++ tailWord_7165985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7165985).length < 2 ^ (prefixWord ++ tailWord_7165985).sum := by decide
  have hdescent : baseEnd_7165985 < baseStart_7165985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7165985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166028 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_7166028 : Nat := 118140960795 + 7166028 * 2 ^ 59
def prefixEnd_7166028 : Nat := 4983230072969 + 3 ^ 40 * 7166028 * 2
def baseEnd_7166028 : Nat := 1226538915859131372064681

theorem tailTrace_7166028 : CollatzResearch.WordTrace tailWord_7166028 prefixEnd_7166028 1226538915859131372064681 := by
  unfold tailWord_7166028
  simp only [CollatzResearch.WordTrace]
  refine ⟨130683256641355945495513369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174244342188474593994017825 130683256641355945495513369)
  ·
    refine ⟨98012442481016959121635027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130683256641355945495513369 98012442481016959121635027)
    ·
      refine ⟨147018663721525438682452541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98012442481016959121635027 147018663721525438682452541)
      ·
        refine ⟨55131998895572039505919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147018663721525438682452541 55131998895572039505919703)
        ·
          refine ⟨82697998343358059258879555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55131998895572039505919703 82697998343358059258879555)
          ·
            refine ⟨124046997515037088888319333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82697998343358059258879555 124046997515037088888319333)
            ·
              refine ⟨23258812034069454166559875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124046997515037088888319333 23258812034069454166559875)
              ·
                refine ⟨34888218051104181249839813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23258812034069454166559875 34888218051104181249839813)
                ·
                  refine ⟨6541540884582033984344965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34888218051104181249839813 6541540884582033984344965)
                  ·
                    refine ⟨1226538915859131372064681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541540884582033984344965 1226538915859131372064681)
                    ·
                      rfl

theorem cell23_7166028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_7166028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166028 prefixEnd_7166028 := by exact prefixLift 7166028
  have htrace : WordTrace (prefixWord ++ tailWord_7166028) baseStart_7166028 baseEnd_7166028 := by
    simpa [prefixWord, tailWord_7166028, baseEnd_7166028] using wordTrace_append hprefix tailTrace_7166028
  have hstable : (prefixWord ++ tailWord_7166028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166028).length < 2 ^ (prefixWord ++ tailWord_7166028).sum := by decide
  have hdescent : baseEnd_7166028 < baseStart_7166028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166031 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_7166031 : Nat := 118140960795 + 7166031 * 2 ^ 59
def prefixEnd_7166031 : Nat := 4983230072969 + 3 ^ 40 * 7166031 * 2
def baseEnd_7166031 : Nat := 3679618288019357604456529

theorem tailTrace_7166031 : CollatzResearch.WordTrace tailWord_7166031 prefixEnd_7166031 3679618288019357604456529 := by
  unfold tailWord_7166031
  simp only [CollatzResearch.WordTrace]
  refine ⟨261366622701701022503385947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174244415134467348335590631 261366622701701022503385947)
  ·
    refine ⟨392049934052551533755078921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261366622701701022503385947 392049934052551533755078921)
    ·
      refine ⟨294037450539413650316309191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392049934052551533755078921 294037450539413650316309191)
      ·
        refine ⟨441056175809120475474463787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294037450539413650316309191 441056175809120475474463787)
        ·
          refine ⟨661584263713680713211695681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441056175809120475474463787 661584263713680713211695681)
          ·
            refine ⟨496188197785260534908771761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661584263713680713211695681 496188197785260534908771761)
            ·
              refine ⟨372141148338945401181578821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496188197785260534908771761 372141148338945401181578821)
              ·
                refine ⟨69776465313552262721546029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372141148338945401181578821 69776465313552262721546029)
                ·
                  refine ⟨26166174492582098520579761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69776465313552262721546029 26166174492582098520579761)
                  ·
                    refine ⟨19624630869436573890434821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26166174492582098520579761 19624630869436573890434821)
                    ·
                      refine ⟨3679618288019357604456529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19624630869436573890434821 3679618288019357604456529)
                      ·
                        rfl

theorem cell23_7166031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_7166031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166031 prefixEnd_7166031 := by exact prefixLift 7166031
  have htrace : WordTrace (prefixWord ++ tailWord_7166031) baseStart_7166031 baseEnd_7166031 := by
    simpa [prefixWord, tailWord_7166031, baseEnd_7166031] using wordTrace_append hprefix tailTrace_7166031
  have hstable : (prefixWord ++ tailWord_7166031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166031).length < 2 ^ (prefixWord ++ tailWord_7166031).sum := by decide
  have hdescent : baseEnd_7166031 < baseStart_7166031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166041 : List Nat := [1, 2, 1, 2, 2, 1, 6, 8]
def baseStart_7166041 : Nat := 118140960795 + 7166041 * 2 ^ 59
def prefixEnd_7166041 : Nat := 4983230072969 + 3 ^ 40 * 7166041 * 2
def baseEnd_7166041 : Nat := 136282348993551946864129

theorem tailTrace_7166041 : CollatzResearch.WordTrace tailWord_7166041 prefixEnd_7166041 136282348993551946864129 := by
  unfold tailWord_7166041
  simp only [CollatzResearch.WordTrace]
  refine ⟨261366987431664794211249977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174244658287776529474166651 261366987431664794211249977)
  ·
    refine ⟨196025240573748595658437483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261366987431664794211249977 196025240573748595658437483)
    ·
      refine ⟨294037860860622893487656225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196025240573748595658437483 294037860860622893487656225)
      ·
        refine ⟨220528395645467170115742169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294037860860622893487656225 220528395645467170115742169)
        ·
          refine ⟨165396296734100377586806627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220528395645467170115742169 165396296734100377586806627)
          ·
            refine ⟨248094445101150566380209941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165396296734100377586806627 248094445101150566380209941)
            ·
              refine ⟨11629427114116432799072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248094445101150566380209941 11629427114116432799072341)
              ·
                refine ⟨136282348993551946864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11629427114116432799072341 136282348993551946864129)
                ·
                  rfl

theorem cell23_7166041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 8].length) (baseStart_7166041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166041 prefixEnd_7166041 := by exact prefixLift 7166041
  have htrace : WordTrace (prefixWord ++ tailWord_7166041) baseStart_7166041 baseEnd_7166041 := by
    simpa [prefixWord, tailWord_7166041, baseEnd_7166041] using wordTrace_append hprefix tailTrace_7166041
  have hstable : (prefixWord ++ tailWord_7166041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166041).length < 2 ^ (prefixWord ++ tailWord_7166041).sum := by decide
  have hdescent : baseEnd_7166041 < baseStart_7166041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166088 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_7166088 : Nat := 118140960795 + 7166088 * 2 ^ 59
def prefixEnd_7166088 : Nat := 4983230072969 + 3 ^ 40 * 7166088 * 2
def baseEnd_7166088 : Nat := 1226549185472221293814589

theorem tailTrace_7166088 : CollatzResearch.WordTrace tailWord_7166088 prefixEnd_7166088 1226549185472221293814589 := by
  unfold tailWord_7166088
  simp only [CollatzResearch.WordTrace]
  refine ⟨130684350831247260619105459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174245801108329680825473945 130684350831247260619105459)
  ·
    refine ⟨196026526246870890928658189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130684350831247260619105459 196026526246870890928658189)
    ·
      refine ⟨73509947342576584098246821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196026526246870890928658189 73509947342576584098246821)
      ·
        refine ⟨13783115126733109518421279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73509947342576584098246821 13783115126733109518421279)
        ·
          refine ⟨20674672690099664277631919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13783115126733109518421279 20674672690099664277631919)
          ·
            refine ⟨31012009035149496416447879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20674672690099664277631919 31012009035149496416447879)
            ·
              refine ⟨46518013552724244624671819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31012009035149496416447879 46518013552724244624671819)
              ·
                refine ⟨69777020329086366937007729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46518013552724244624671819 69777020329086366937007729)
                ·
                  refine ⟨52332765246814775202755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69777020329086366937007729 52332765246814775202755797)
                  ·
                    refine ⟨1226549185472221293814589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52332765246814775202755797 1226549185472221293814589)
                    ·
                      rfl

theorem cell23_7166088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_7166088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166088 prefixEnd_7166088 := by exact prefixLift 7166088
  have htrace : WordTrace (prefixWord ++ tailWord_7166088) baseStart_7166088 baseEnd_7166088 := by
    simpa [prefixWord, tailWord_7166088, baseEnd_7166088] using wordTrace_append hprefix tailTrace_7166088
  have hstable : (prefixWord ++ tailWord_7166088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166088).length < 2 ^ (prefixWord ++ tailWord_7166088).sum := by decide
  have hdescent : baseEnd_7166088 < baseStart_7166088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166108 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7166108 : Nat := 118140960795 + 7166108 * 2 ^ 59
def prefixEnd_7166108 : Nat := 4983230072969 + 3 ^ 40 * 7166108 * 2
def baseEnd_7166108 : Nat := 3679657826029753803193675

theorem tailTrace_7166108 : CollatzResearch.WordTrace tailWord_7166108 prefixEnd_7166108 3679657826029753803193675 := by
  unfold tailWord_7166108
  simp only [CollatzResearch.WordTrace]
  refine ⟨130684715561211032326969489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174246287414948043102625985 130684715561211032326969489)
  ·
    refine ⟨98013536670908274245227117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130684715561211032326969489 98013536670908274245227117)
    ·
      refine ⟨36755076251590602841960169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98013536670908274245227117 36755076251590602841960169)
      ·
        refine ⟨27566307188692952131470127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36755076251590602841960169 27566307188692952131470127)
        ·
          refine ⟨41349460783039428197205191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27566307188692952131470127 41349460783039428197205191)
          ·
            refine ⟨62024191174559142295807787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41349460783039428197205191 62024191174559142295807787)
            ·
              refine ⟨93036286761838713443711681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62024191174559142295807787 93036286761838713443711681)
              ·
                refine ⟨69777215071379035082783761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93036286761838713443711681 69777215071379035082783761)
                ·
                  refine ⟨52332911303534276312087821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69777215071379035082783761 52332911303534276312087821)
                  ·
                    refine ⟨19624841738825353617032933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52332911303534276312087821 19624841738825353617032933)
                    ·
                      refine ⟨3679657826029753803193675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19624841738825353617032933 3679657826029753803193675)
                      ·
                        rfl

theorem cell23_7166108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7166108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166108 prefixEnd_7166108 := by exact prefixLift 7166108
  have htrace : WordTrace (prefixWord ++ tailWord_7166108) baseStart_7166108 baseEnd_7166108 := by
    simpa [prefixWord, tailWord_7166108, baseEnd_7166108] using wordTrace_append hprefix tailTrace_7166108
  have hstable : (prefixWord ++ tailWord_7166108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166108).length < 2 ^ (prefixWord ++ tailWord_7166108).sum := by decide
  have hdescent : baseEnd_7166108 < baseStart_7166108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166129 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7166129 : Nat := 118140960795 + 7166129 * 2 ^ 59
def prefixEnd_7166129 : Nat := 4983230072969 + 3 ^ 40 * 7166129 * 2
def baseEnd_7166129 : Nat := 3679668609123498221031079

theorem tailTrace_7166129 : CollatzResearch.WordTrace tailWord_7166129 prefixEnd_7166129 3679668609123498221031079 := by
  unfold tailWord_7166129
  simp only [CollatzResearch.WordTrace]
  refine ⟨261370197055345985240453441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174246798036897323493635627 261370197055345985240453441)
  ·
    refine ⟨196027647791509488930340081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261370197055345985240453441 196027647791509488930340081)
    ·
      refine ⟨147020735843632116697755061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196027647791509488930340081 147020735843632116697755061)
      ·
        refine ⟨13783193985340510940414537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147020735843632116697755061 13783193985340510940414537)
        ·
          refine ⟨10337395489005383205310903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13783193985340510940414537 10337395489005383205310903)
          ·
            refine ⟨15506093233508074807966355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337395489005383205310903 15506093233508074807966355)
            ·
              refine ⟨23259139850262112211949533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506093233508074807966355 23259139850262112211949533)
              ·
                refine ⟨8722177443848292079481075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23259139850262112211949533 8722177443848292079481075)
                ·
                  refine ⟨13083266165772438119221613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722177443848292079481075 13083266165772438119221613)
                  ·
                    refine ⟨4906224812164664294708105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13083266165772438119221613 4906224812164664294708105)
                    ·
                      refine ⟨3679668609123498221031079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906224812164664294708105 3679668609123498221031079)
                      ·
                        rfl

theorem cell23_7166129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7166129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166129 prefixEnd_7166129 := by exact prefixLift 7166129
  have htrace : WordTrace (prefixWord ++ tailWord_7166129) baseStart_7166129 baseEnd_7166129 := by
    simpa [prefixWord, tailWord_7166129, baseEnd_7166129] using wordTrace_append hprefix tailTrace_7166129
  have hstable : (prefixWord ++ tailWord_7166129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166129).length < 2 ^ (prefixWord ++ tailWord_7166129).sum := by decide
  have hdescent : baseEnd_7166129 < baseStart_7166129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166131 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 11]
def baseStart_7166131 : Nat := 118140960795 + 7166131 * 2 ^ 59
def prefixEnd_7166131 : Nat := 4983230072969 + 3 ^ 40 * 7166131 * 2
def baseEnd_7166131 : Nat := 408852181787200801467341

theorem tailTrace_7166131 : CollatzResearch.WordTrace tailWord_7166131 prefixEnd_7166131 408852181787200801467341 := by
  unfold tailWord_7166131
  simp only [CollatzResearch.WordTrace]
  refine ⟨261370270001338739582026247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174246846667559159721350831 261370270001338739582026247)
  ·
    refine ⟨392055405002008109373039371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261370270001338739582026247 392055405002008109373039371)
    ·
      refine ⟨588083107503012164059559057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392055405002008109373039371 588083107503012164059559057)
      ·
        refine ⟨441062330627259123044669293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588083107503012164059559057 441062330627259123044669293)
        ·
          refine ⟨165398373985222171141750985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441062330627259123044669293 165398373985222171141750985)
          ·
            refine ⟨124048780488916628356313239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165398373985222171141750985 124048780488916628356313239)
            ·
              refine ⟨186073170733374942534469859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124048780488916628356313239 186073170733374942534469859)
              ·
                refine ⟨279109756100062413801704789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186073170733374942534469859 279109756100062413801704789)
                ·
                  refine ⟨408852181787200801467341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 279109756100062413801704789 408852181787200801467341)
                  ·
                    rfl

theorem cell23_7166131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 11].length) (baseStart_7166131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166131 prefixEnd_7166131 := by exact prefixLift 7166131
  have htrace : WordTrace (prefixWord ++ tailWord_7166131) baseStart_7166131 baseEnd_7166131 := by
    simpa [prefixWord, tailWord_7166131, baseEnd_7166131] using wordTrace_append hprefix tailTrace_7166131
  have hstable : (prefixWord ++ tailWord_7166131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166131).length < 2 ^ (prefixWord ++ tailWord_7166131).sum := by decide
  have hdescent : baseEnd_7166131 < baseStart_7166131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166138 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_7166138 : Nat := 118140960795 + 7166138 * 2 ^ 59
def prefixEnd_7166138 : Nat := 4983230072969 + 3 ^ 40 * 7166138 * 2
def baseEnd_7166138 : Nat := 3679673230449388685818537

theorem tailTrace_7166138 : CollatzResearch.WordTrace tailWord_7166138 prefixEnd_7166138 3679673230449388685818537 := by
  unfold tailWord_7166138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65342631328078344944382767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174247016874875586518354045 65342631328078344944382767)
  ·
    refine ⟨98013946992117517416574151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65342631328078344944382767 98013946992117517416574151)
    ·
      refine ⟨147020920488176276124861227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98013946992117517416574151 147020920488176276124861227)
      ·
        refine ⟨220531380732264414187291841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147020920488176276124861227 220531380732264414187291841)
        ·
          refine ⟨165398535549198310640468881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220531380732264414187291841 165398535549198310640468881)
          ·
            refine ⟨124048901661898732980351661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165398535549198310640468881 124048901661898732980351661)
            ·
              refine ⟨46518338123212024867631873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124048901661898732980351661 46518338123212024867631873)
              ·
                refine ⟨34888753592409018650723905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46518338123212024867631873 34888753592409018650723905)
                ·
                  refine ⟨26166565194306763988042929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34888753592409018650723905 26166565194306763988042929)
                  ·
                    refine ⟨19624923895730072991032197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26166565194306763988042929 19624923895730072991032197)
                    ·
                      refine ⟨3679673230449388685818537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19624923895730072991032197 3679673230449388685818537)
                      ·
                        rfl

theorem cell23_7166138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_7166138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166138 prefixEnd_7166138 := by exact prefixLift 7166138
  have htrace : WordTrace (prefixWord ++ tailWord_7166138) baseStart_7166138 baseEnd_7166138 := by
    simpa [prefixWord, tailWord_7166138, baseEnd_7166138] using wordTrace_append hprefix tailTrace_7166138
  have hstable : (prefixWord ++ tailWord_7166138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166138).length < 2 ^ (prefixWord ++ tailWord_7166138).sum := by decide
  have hdescent : baseEnd_7166138 < baseStart_7166138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166159 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 2, 2, 2]
def baseStart_7166159 : Nat := 118140960795 + 7166159 * 2 ^ 59
def prefixEnd_7166159 : Nat := 4983230072969 + 3 ^ 40 * 7166159 * 2
def baseEnd_7166159 : Nat := 3679684013543133103655941

theorem tailTrace_7166159 : CollatzResearch.WordTrace tailWord_7166159 prefixEnd_7166159 3679684013543133103655941 := by
  unfold tailWord_7166159
  simp only [CollatzResearch.WordTrace]
  refine ⟨261371291245237300364045531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174247527496824866909363687 261371291245237300364045531)
  ·
    refine ⟨392056936867855950546068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261371291245237300364045531 392056936867855950546068297)
    ·
      refine ⟨294042702650891962909551223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392056936867855950546068297 294042702650891962909551223)
      ·
        refine ⟨441064053976337944364326835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294042702650891962909551223 441064053976337944364326835)
        ·
          refine ⟨661596080964506916546490253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441064053976337944364326835 661596080964506916546490253)
          ·
            refine ⟨248098530361690093704933845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661596080964506916546490253 248098530361690093704933845)
            ·
              refine ⟨5814809305352111571209387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248098530361690093704933845 5814809305352111571209387)
              ·
                refine ⟨8722213958028167356814081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814809305352111571209387 8722213958028167356814081)
                ·
                  refine ⟨6541660468521125517610561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8722213958028167356814081 6541660468521125517610561)
                  ·
                    refine ⟨4906245351390844138207921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6541660468521125517610561 4906245351390844138207921)
                    ·
                      refine ⟨3679684013543133103655941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906245351390844138207921 3679684013543133103655941)
                      ·
                        rfl

theorem cell23_7166159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 2, 2].length) (baseStart_7166159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166159 prefixEnd_7166159 := by exact prefixLift 7166159
  have htrace : WordTrace (prefixWord ++ tailWord_7166159) baseStart_7166159 baseEnd_7166159 := by
    simpa [prefixWord, tailWord_7166159, baseEnd_7166159] using wordTrace_append hprefix tailTrace_7166159
  have hstable : (prefixWord ++ tailWord_7166159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166159).length < 2 ^ (prefixWord ++ tailWord_7166159).sum := by decide
  have hdescent : baseEnd_7166159 < baseStart_7166159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166188 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_7166188 : Nat := 118140960795 + 7166188 * 2 ^ 59
def prefixEnd_7166188 : Nat := 4983230072969 + 3 ^ 40 * 7166188 * 2
def baseEnd_7166188 : Nat := 3679698904482113490193307

theorem tailTrace_7166188 : CollatzResearch.WordTrace tailWord_7166188 prefixEnd_7166188 3679698904482113490193307 := by
  unfold tailWord_7166188
  simp only [CollatzResearch.WordTrace]
  refine ⟨130686174481066119158425609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174248232641421492211234145 130686174481066119158425609)
  ·
    refine ⟨98014630860799589368819207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130686174481066119158425609 98014630860799589368819207)
    ·
      refine ⟨147021946291199384053228811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98014630860799589368819207 147021946291199384053228811)
      ·
        refine ⟨220532919436799076079843217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147021946291199384053228811 220532919436799076079843217)
        ·
          refine ⟨165399689577599307059882413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220532919436799076079843217 165399689577599307059882413)
          ·
            refine ⟨62024883591599740147455905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165399689577599307059882413 62024883591599740147455905)
            ·
              refine ⟨46518662693699805110591929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62024883591599740147455905 46518662693699805110591929)
              ·
                refine ⟨34888997020274853832943947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46518662693699805110591929 34888997020274853832943947)
                ·
                  refine ⟨52333495530412280749415921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34888997020274853832943947 52333495530412280749415921)
                  ·
                    refine ⟨39250121647809210562061941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52333495530412280749415921 39250121647809210562061941)
                    ·
                      refine ⟨3679698904482113490193307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39250121647809210562061941 3679698904482113490193307)
                      ·
                        rfl

theorem cell23_7166188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_7166188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166188 prefixEnd_7166188 := by exact prefixLift 7166188
  have htrace : WordTrace (prefixWord ++ tailWord_7166188) baseStart_7166188 baseEnd_7166188 := by
    simpa [prefixWord, tailWord_7166188, baseEnd_7166188] using wordTrace_append hprefix tailTrace_7166188
  have hstable : (prefixWord ++ tailWord_7166188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166188).length < 2 ^ (prefixWord ++ tailWord_7166188).sum := by decide
  have hdescent : baseEnd_7166188 < baseStart_7166188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166235 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3]
def baseStart_7166235 : Nat := 118140960795 + 7166235 * 2 ^ 59
def prefixEnd_7166235 : Nat := 4983230072969 + 3 ^ 40 * 7166235 * 2
def baseEnd_7166235 : Nat := 3679723038072874806305591

theorem tailTrace_7166235 : CollatzResearch.WordTrace tailWord_7166235 prefixEnd_7166235 3679723038072874806305591 := by
  unfold tailWord_7166235
  simp only [CollatzResearch.WordTrace]
  refine ⟨261374063192961965343812159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174249375461974643562541439 261374063192961965343812159)
  ·
    refine ⟨392061094789442948015718239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261374063192961965343812159 392061094789442948015718239)
    ·
      refine ⟨588091642184164422023577359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392061094789442948015718239 588091642184164422023577359)
      ·
        refine ⟨882137463276246633035366039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588091642184164422023577359 882137463276246633035366039)
        ·
          refine ⟨1323206194914369949553049059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882137463276246633035366039 1323206194914369949553049059)
          ·
            refine ⟨1984809292371554924329573589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323206194914369949553049059 1984809292371554924329573589)
            ·
              refine ⟨46518967789958318538974381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1984809292371554924329573589 46518967789958318538974381)
              ·
                refine ⟨17444612921234369452115393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46518967789958318538974381 17444612921234369452115393)
                ·
                  refine ⟨13083459690925777089086545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17444612921234369452115393 13083459690925777089086545)
                  ·
                    refine ⟨9812594768194332816814909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13083459690925777089086545 9812594768194332816814909)
                    ·
                      refine ⟨3679723038072874806305591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9812594768194332816814909 3679723038072874806305591)
                      ·
                        rfl

theorem cell23_7166235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].length) (baseStart_7166235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166235 prefixEnd_7166235 := by exact prefixLift 7166235
  have htrace : WordTrace (prefixWord ++ tailWord_7166235) baseStart_7166235 baseEnd_7166235 := by
    simpa [prefixWord, tailWord_7166235, baseEnd_7166235] using wordTrace_append hprefix tailTrace_7166235
  have hstable : (prefixWord ++ tailWord_7166235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166235).length < 2 ^ (prefixWord ++ tailWord_7166235).sum := by decide
  have hdescent : baseEnd_7166235 < baseStart_7166235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166315 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 4, 4]
def baseStart_7166315 : Nat := 118140960795 + 7166315 * 2 ^ 59
def prefixEnd_7166315 : Nat := 4983230072969 + 3 ^ 40 * 7166315 * 2
def baseEnd_7166315 : Nat := 1226588038841744831101741

theorem tailTrace_7166315 : CollatzResearch.WordTrace tailWord_7166315 prefixEnd_7166315 1226588038841744831101741 := by
  unfold tailWord_7166315
  simp only [CollatzResearch.WordTrace]
  refine ⟨261376981032672139006724399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174251320688448092671149599 261376981032672139006724399)
  ·
    refine ⟨392065471549008208510086599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261376981032672139006724399 392065471549008208510086599)
    ·
      refine ⟨588098207323512312765129899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392065471549008208510086599 588098207323512312765129899)
      ·
        refine ⟨882147310985268469147694849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588098207323512312765129899 882147310985268469147694849)
        ·
          refine ⟨661610483238951351860771137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882147310985268469147694849 661610483238951351860771137)
          ·
            refine ⟨496207862429213513895578353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661610483238951351860771137 496207862429213513895578353)
            ·
              refine ⟨372155896821910135421683765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496207862429213513895578353 372155896821910135421683765)
              ·
                refine ⟨34889615327054075195782853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372155896821910135421683765 34889615327054075195782853)
                ·
                  refine ⟨6541802873822639099209285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34889615327054075195782853 6541802873822639099209285)
                  ·
                    refine ⟨1226588038841744831101741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541802873822639099209285 1226588038841744831101741)
                    ·
                      rfl

theorem cell23_7166315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 4].length) (baseStart_7166315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166315 prefixEnd_7166315 := by exact prefixLift 7166315
  have htrace : WordTrace (prefixWord ++ tailWord_7166315) baseStart_7166315 baseEnd_7166315 := by
    simpa [prefixWord, tailWord_7166315, baseEnd_7166315] using wordTrace_append hprefix tailTrace_7166315
  have hstable : (prefixWord ++ tailWord_7166315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166315).length < 2 ^ (prefixWord ++ tailWord_7166315).sum := by decide
  have hdescent : baseEnd_7166315 < baseStart_7166315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166339 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 4]
def baseStart_7166339 : Nat := 118140960795 + 7166339 * 2 ^ 59
def prefixEnd_7166339 : Nat := 4983230072969 + 3 ^ 40 * 7166339 * 2
def baseEnd_7166339 : Nat := 3679776440060942399405113

theorem tailTrace_7166339 : CollatzResearch.WordTrace tailWord_7166339 prefixEnd_7166339 3679776440060942399405113 := by
  unfold tailWord_7166339
  simp only [CollatzResearch.WordTrace]
  refine ⟨261377856384585191105598071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174251904256390127403732047 261377856384585191105598071)
  ·
    refine ⟨392066784576877786658397107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261377856384585191105598071 392066784576877786658397107)
    ·
      refine ⟨588100176865316679987595661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392066784576877786658397107 588100176865316679987595661)
      ·
        refine ⟨220537566324493754995348373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588100176865316679987595661 220537566324493754995348373)
        ·
          refine ⟨10337698421460644765406955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220537566324493754995348373 10337698421460644765406955)
          ·
            refine ⟨15506547632190967148110433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337698421460644765406955 15506547632190967148110433)
            ·
              refine ⟨11629910724143225361082825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15506547632190967148110433 11629910724143225361082825)
              ·
                refine ⟨8722433043107419020812119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629910724143225361082825 8722433043107419020812119)
                ·
                  refine ⟨13083649564661128531218179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722433043107419020812119 13083649564661128531218179)
                  ·
                    refine ⟨19625474346991692796827269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13083649564661128531218179 19625474346991692796827269)
                    ·
                      refine ⟨3679776440060942399405113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19625474346991692796827269 3679776440060942399405113)
                      ·
                        rfl

theorem cell23_7166339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_7166339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166339 prefixEnd_7166339 := by exact prefixLift 7166339
  have htrace : WordTrace (prefixWord ++ tailWord_7166339) baseStart_7166339 baseEnd_7166339 := by
    simpa [prefixWord, tailWord_7166339, baseEnd_7166339] using wordTrace_append hprefix tailTrace_7166339
  have hstable : (prefixWord ++ tailWord_7166339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166339).length < 2 ^ (prefixWord ++ tailWord_7166339).sum := by decide
  have hdescent : baseEnd_7166339 < baseStart_7166339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166345 : List Nat := [1, 2, 1, 1, 6, 2, 1, 9]
def baseStart_7166345 : Nat := 118140960795 + 7166345 * 2 ^ 59
def prefixEnd_7166345 : Nat := 4983230072969 + 3 ^ 40 * 7166345 * 2
def baseEnd_7166345 : Nat := 136288130405365532441855

theorem tailTrace_7166345 : CollatzResearch.WordTrace tailWord_7166345 prefixEnd_7166345 136288130405365532441855 := by
  unfold tailWord_7166345
  simp only [CollatzResearch.WordTrace]
  refine ⟨261378075222563454130316489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174252050148375636086877659 261378075222563454130316489)
  ·
    refine ⟨196033556416922590597737367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261378075222563454130316489 196033556416922590597737367)
    ·
      refine ⟨294050334625383885896606051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196033556416922590597737367 294050334625383885896606051)
      ·
        refine ⟨441075501938075828844909077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294050334625383885896606051 441075501938075828844909077)
        ·
          refine ⟨20675414153347304477105113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 441075501938075828844909077 20675414153347304477105113)
          ·
            refine ⟨15506560615010478357828835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20675414153347304477105113 15506560615010478357828835)
            ·
              refine ⟨23259840922515717536743253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506560615010478357828835 23259840922515717536743253)
              ·
                refine ⟨136288130405365532441855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23259840922515717536743253 136288130405365532441855)
                ·
                  rfl

theorem cell23_7166345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 9].length) (baseStart_7166345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166345 prefixEnd_7166345 := by exact prefixLift 7166345
  have htrace : WordTrace (prefixWord ++ tailWord_7166345) baseStart_7166345 baseEnd_7166345 := by
    simpa [prefixWord, tailWord_7166345, baseEnd_7166345] using wordTrace_append hprefix tailTrace_7166345
  have hstable : (prefixWord ++ tailWord_7166345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166345).length < 2 ^ (prefixWord ++ tailWord_7166345).sum := by decide
  have hdescent : baseEnd_7166345 < baseStart_7166345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166373 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_7166373 : Nat := 118140960795 + 7166373 * 2 ^ 59
def prefixEnd_7166373 : Nat := 4983230072969 + 3 ^ 40 * 7166373 * 2
def baseEnd_7166373 : Nat := 3679793898403195266379957

theorem tailTrace_7166373 : CollatzResearch.WordTrace tailWord_7166373 prefixEnd_7166373 3679793898403195266379957 := by
  unfold tailWord_7166373
  simp only [CollatzResearch.WordTrace]
  refine ⟨261379096466462014912335773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174252730977641343274890515 261379096466462014912335773)
  ·
    refine ⟨98017161174923255592125915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261379096466462014912335773 98017161174923255592125915)
    ·
      refine ⟨147025741762384883388188873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98017161174923255592125915 147025741762384883388188873)
      ·
        refine ⟨110269306321788662541141655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147025741762384883388188873 110269306321788662541141655)
        ·
          refine ⟨165403959482682993811712483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110269306321788662541141655 165403959482682993811712483)
          ·
            refine ⟨248105939224024490717568725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165403959482682993811712483 248105939224024490717568725)
            ·
              refine ⟨5814982950563074001193017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248105939224024490717568725 5814982950563074001193017)
              ·
                refine ⟨4361237212922305500894763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814982950563074001193017 4361237212922305500894763)
                ·
                  refine ⟨6541855819383458251342145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361237212922305500894763 6541855819383458251342145)
                  ·
                    refine ⟨4906391864537593688506609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6541855819383458251342145 4906391864537593688506609)
                    ·
                      refine ⟨3679793898403195266379957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906391864537593688506609 3679793898403195266379957)
                      ·
                        rfl

theorem cell23_7166373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_7166373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166373 prefixEnd_7166373 := by exact prefixLift 7166373
  have htrace : WordTrace (prefixWord ++ tailWord_7166373) baseStart_7166373 baseEnd_7166373 := by
    simpa [prefixWord, tailWord_7166373, baseEnd_7166373] using wordTrace_append hprefix tailTrace_7166373
  have hstable : (prefixWord ++ tailWord_7166373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166373).length < 2 ^ (prefixWord ++ tailWord_7166373).sum := by decide
  have hdescent : baseEnd_7166373 < baseStart_7166373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166429 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_7166429 : Nat := 118140960795 + 7166429 * 2 ^ 59
def prefixEnd_7166429 : Nat := 4983230072969 + 3 ^ 40 * 7166429 * 2
def baseEnd_7166429 : Nat := 3679822653319847047279699

theorem tailTrace_7166429 : CollatzResearch.WordTrace tailWord_7166429 prefixEnd_7166429 3679822653319847047279699 := by
  unfold tailWord_7166429
  simp only [CollatzResearch.WordTrace]
  refine ⟨261381138954259136476374341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174254092636172757650916227 261381138954259136476374341)
  ·
    refine ⟨49008963553923588089320189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261381138954259136476374341 49008963553923588089320189)
    ·
      refine ⟨18378361332721345533495071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49008963553923588089320189 18378361332721345533495071)
      ·
        refine ⟨27567541999082018300242607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378361332721345533495071 27567541999082018300242607)
        ·
          refine ⟨41351312998623027450363911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27567541999082018300242607 41351312998623027450363911)
          ·
            refine ⟨62026969497934541175545867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41351312998623027450363911 62026969497934541175545867)
            ·
              refine ⟨93040454246901811763318801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62026969497934541175545867 93040454246901811763318801)
              ·
                refine ⟨69780340685176358822489101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93040454246901811763318801 69780340685176358822489101)
                ·
                  refine ⟨26167627756941134558433413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69780340685176358822489101 26167627756941134558433413)
                  ·
                    refine ⟨4906430204426462729706265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26167627756941134558433413 4906430204426462729706265)
                    ·
                      refine ⟨3679822653319847047279699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906430204426462729706265 3679822653319847047279699)
                      ·
                        rfl

theorem cell23_7166429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_7166429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166429 prefixEnd_7166429 := by exact prefixLift 7166429
  have htrace : WordTrace (prefixWord ++ tailWord_7166429) baseStart_7166429 baseEnd_7166429 := by
    simpa [prefixWord, tailWord_7166429, baseEnd_7166429] using wordTrace_append hprefix tailTrace_7166429
  have hstable : (prefixWord ++ tailWord_7166429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166429).length < 2 ^ (prefixWord ++ tailWord_7166429).sum := by decide
  have hdescent : baseEnd_7166429 < baseStart_7166429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166442 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7166442 : Nat := 118140960795 + 7166442 * 2 ^ 59
def prefixEnd_7166442 : Nat := 4983230072969 + 3 ^ 40 * 7166442 * 2
def baseEnd_7166442 : Nat := 3679829328568355496417139

theorem tailTrace_7166442 : CollatzResearch.WordTrace tailWord_7166442 prefixEnd_7166442 3679829328568355496417139 := by
  unfold tailWord_7166442
  simp only [CollatzResearch.WordTrace]
  refine ⟨65345403275803009924149395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174254408735474693131065053 65345403275803009924149395)
  ·
    refine ⟨98018104913704514886224093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65345403275803009924149395 98018104913704514886224093)
    ·
      refine ⟨36756789342639193082334035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98018104913704514886224093 36756789342639193082334035)
      ·
        refine ⟨55135184013958789623501053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36756789342639193082334035 55135184013958789623501053)
        ·
          refine ⟨20675694005234546108812895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55135184013958789623501053 20675694005234546108812895)
          ·
            refine ⟨31013541007851819163219343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20675694005234546108812895 31013541007851819163219343)
            ·
              refine ⟨46520311511777728744829015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31013541007851819163219343 46520311511777728744829015)
              ·
                refine ⟨69780467267666593117243523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46520311511777728744829015 69780467267666593117243523)
                ·
                  refine ⟨104670700901499889675865285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69780467267666593117243523 104670700901499889675865285)
                  ·
                    refine ⟨19625756419031229314224741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104670700901499889675865285 19625756419031229314224741)
                    ·
                      refine ⟨3679829328568355496417139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19625756419031229314224741 3679829328568355496417139)
                      ·
                        rfl

theorem cell23_7166442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7166442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166442 prefixEnd_7166442 := by exact prefixLift 7166442
  have htrace : WordTrace (prefixWord ++ tailWord_7166442) baseStart_7166442 baseEnd_7166442 := by
    simpa [prefixWord, tailWord_7166442, baseEnd_7166442] using wordTrace_append hprefix tailTrace_7166442
  have hstable : (prefixWord ++ tailWord_7166442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166442).length < 2 ^ (prefixWord ++ tailWord_7166442).sum := by decide
  have hdescent : baseEnd_7166442 < baseStart_7166442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166446 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_7166446 : Nat := 118140960795 + 7166446 * 2 ^ 59
def prefixEnd_7166446 : Nat := 4983230072969 + 3 ^ 40 * 7166446 * 2
def baseEnd_7166446 : Nat := 3679831382490973480767121

theorem tailTrace_7166446 : CollatzResearch.WordTrace tailWord_7166446 prefixEnd_7166446 3679831382490973480767121 := by
  unfold tailWord_7166446
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672719874399693547467899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174254505996798365586495461 32672719874399693547467899)
  ·
    refine ⟨49009079811599540321201849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32672719874399693547467899 49009079811599540321201849)
    ·
      refine ⟨36756809858699655240901387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49009079811599540321201849 36756809858699655240901387)
      ·
        refine ⟨55135214788049482861352081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36756809858699655240901387 55135214788049482861352081)
        ·
          refine ⟨41351411091037112146014061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55135214788049482861352081 41351411091037112146014061)
          ·
            refine ⟨15506779159138917054755273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41351411091037112146014061 15506779159138917054755273)
            ·
              refine ⟨11630084369354187791066455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15506779159138917054755273 11630084369354187791066455)
              ·
                refine ⟨17445126554031281686599683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630084369354187791066455 17445126554031281686599683)
                ·
                  refine ⟨26167689831046922529899525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17445126554031281686599683 26167689831046922529899525)
                  ·
                    refine ⟨4906441843321297974356161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26167689831046922529899525 4906441843321297974356161)
                    ·
                      refine ⟨3679831382490973480767121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906441843321297974356161 3679831382490973480767121)
                      ·
                        rfl

theorem cell23_7166446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_7166446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166446 prefixEnd_7166446 := by exact prefixLift 7166446
  have htrace : WordTrace (prefixWord ++ tailWord_7166446) baseStart_7166446 baseEnd_7166446 := by
    simpa [prefixWord, tailWord_7166446, baseEnd_7166446] using wordTrace_append hprefix tailTrace_7166446
  have hstable : (prefixWord ++ tailWord_7166446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166446).length < 2 ^ (prefixWord ++ tailWord_7166446).sum := by decide
  have hdescent : baseEnd_7166446 < baseStart_7166446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166542 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_7166542 : Nat := 118140960795 + 7166542 * 2 ^ 59
def prefixEnd_7166542 : Nat := 4983230072969 + 3 ^ 40 * 7166542 * 2
def baseEnd_7166542 : Nat := 408875630737089456129631

theorem tailTrace_7166542 : CollatzResearch.WordTrace tailWord_7166542 prefixEnd_7166542 408875630737089456129631 := by
  unfold tailWord_7166542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673157550356219596904735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174256840268566504516825253 32673157550356219596904735)
  ·
    refine ⟨49009736325534329395357103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32673157550356219596904735 49009736325534329395357103)
    ·
      refine ⟨73514604488301494093035655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49009736325534329395357103 73514604488301494093035655)
      ·
        refine ⟨110271906732452241139553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73514604488301494093035655 110271906732452241139553483)
        ·
          refine ⟨165407860098678361709330225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110271906732452241139553483 165407860098678361709330225)
          ·
            refine ⟨124055895074008771281997669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165407860098678361709330225 124055895074008771281997669)
            ·
              refine ⟨23260480326376644615374563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124055895074008771281997669 23260480326376644615374563)
              ·
                refine ⟨34890720489564966923061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23260480326376644615374563 34890720489564966923061845)
                ·
                  refine ⟨408875630737089456129631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34890720489564966923061845 408875630737089456129631)
                  ·
                    rfl

theorem cell23_7166542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_7166542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166542 prefixEnd_7166542 := by exact prefixLift 7166542
  have htrace : WordTrace (prefixWord ++ tailWord_7166542) baseStart_7166542 baseEnd_7166542 := by
    simpa [prefixWord, tailWord_7166542, baseEnd_7166542] using wordTrace_append hprefix tailTrace_7166542
  have hstable : (prefixWord ++ tailWord_7166542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166542).length < 2 ^ (prefixWord ++ tailWord_7166542).sum := by decide
  have hdescent : baseEnd_7166542 < baseStart_7166542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166569 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_7166569 : Nat := 118140960795 + 7166569 * 2 ^ 59
def prefixEnd_7166569 : Nat := 4983230072969 + 3 ^ 40 * 7166569 * 2
def baseEnd_7166569 : Nat := 3679894540611476499529055

theorem tailTrace_7166569 : CollatzResearch.WordTrace tailWord_7166569 prefixEnd_7166569 3679894540611476499529055 := by
  unfold tailWord_7166569
  simp only [CollatzResearch.WordTrace]
  refine ⟨261386245173751940386470761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174257496782501293590980507 261386245173751940386470761)
  ·
    refine ⟨196039683880313955289853071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261386245173751940386470761 196039683880313955289853071)
    ·
      refine ⟨294059525820470932934779607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196039683880313955289853071 294059525820470932934779607)
      ·
        refine ⟨441089288730706399402169411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294059525820470932934779607 441089288730706399402169411)
        ·
          refine ⟨661633933096059599103254117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441089288730706399402169411 661633933096059599103254117)
          ·
            refine ⟨124056362455511174831860147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 661633933096059599103254117 124056362455511174831860147)
            ·
              refine ⟨186084543683266762247790221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124056362455511174831860147 186084543683266762247790221)
              ·
                refine ⟨69781703881225035842921333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186084543683266762247790221 69781703881225035842921333)
                ·
                  refine ⟨6542034738864847110273875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69781703881225035842921333 6542034738864847110273875)
                  ·
                    refine ⟨9813052108297270665410813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542034738864847110273875 9813052108297270665410813)
                    ·
                      refine ⟨3679894540611476499529055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813052108297270665410813 3679894540611476499529055)
                      ·
                        rfl

theorem cell23_7166569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_7166569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166569 prefixEnd_7166569 := by exact prefixLift 7166569
  have htrace : WordTrace (prefixWord ++ tailWord_7166569) baseStart_7166569 baseEnd_7166569 := by
    simpa [prefixWord, tailWord_7166569, baseEnd_7166569] using wordTrace_append hprefix tailTrace_7166569
  have hstable : (prefixWord ++ tailWord_7166569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166569).length < 2 ^ (prefixWord ++ tailWord_7166569).sum := by decide
  have hdescent : baseEnd_7166569 < baseStart_7166569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166639 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_7166639 : Nat := 118140960795 + 7166639 * 2 ^ 59
def prefixEnd_7166639 : Nat := 4983230072969 + 3 ^ 40 * 7166639 * 2
def baseEnd_7166639 : Nat := 3679930484257291225653733

theorem tailTrace_7166639 : CollatzResearch.WordTrace tailWord_7166639 prefixEnd_7166639 3679930484257291225653733 := by
  unfold tailWord_7166639
  simp only [CollatzResearch.WordTrace]
  refine ⟨261388798283498342341518971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174259198855665561561012647 261388798283498342341518971)
  ·
    refine ⟨392083197425247513512278457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261388798283498342341518971 392083197425247513512278457)
    ·
      refine ⟨294062398068935635134208843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392083197425247513512278457 294062398068935635134208843)
      ·
        refine ⟨441093597103403452701313265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294062398068935635134208843 441093597103403452701313265)
        ·
          refine ⟨330820197827552589525984949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441093597103403452701313265 330820197827552589525984949)
          ·
            refine ⟨31014393546333055268061089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330820197827552589525984949 31014393546333055268061089)
            ·
              refine ⟨23260795159749791451045817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31014393546333055268061089 23260795159749791451045817)
              ·
                refine ⟨17445596369812343588284363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23260795159749791451045817 17445596369812343588284363)
                ·
                  refine ⟨26168394554718515382426545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17445596369812343588284363 26168394554718515382426545)
                  ·
                    refine ⟨19626295916038886536819909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26168394554718515382426545 19626295916038886536819909)
                    ·
                      refine ⟨3679930484257291225653733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19626295916038886536819909 3679930484257291225653733)
                      ·
                        rfl

theorem cell23_7166639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_7166639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166639 prefixEnd_7166639 := by exact prefixLift 7166639
  have htrace : WordTrace (prefixWord ++ tailWord_7166639) baseStart_7166639 baseEnd_7166639 := by
    simpa [prefixWord, tailWord_7166639, baseEnd_7166639] using wordTrace_append hprefix tailTrace_7166639
  have hstable : (prefixWord ++ tailWord_7166639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166639).length < 2 ^ (prefixWord ++ tailWord_7166639).sum := by decide
  have hdescent : baseEnd_7166639 < baseStart_7166639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166643 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 1, 1, 4]
def baseStart_7166643 : Nat := 118140960795 + 7166643 * 2 ^ 59
def prefixEnd_7166643 : Nat := 4983230072969 + 3 ^ 40 * 7166643 * 2
def baseEnd_7166643 : Nat := 3679932538179909210003715

theorem tailTrace_7166643 : CollatzResearch.WordTrace tailWord_7166643 prefixEnd_7166643 3679932538179909210003715 := by
  unfold tailWord_7166643
  simp only [CollatzResearch.WordTrace]
  refine ⟨261388944175483851024664583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174259296116989234016443055 261388944175483851024664583)
  ·
    refine ⟨392083416263225776536996875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261388944175483851024664583 392083416263225776536996875)
    ·
      refine ⟨588125124394838664805495313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392083416263225776536996875 588125124394838664805495313)
      ·
        refine ⟨441093843296128998604121485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588125124394838664805495313 441093843296128998604121485)
        ·
          refine ⟨165410191236048374476545557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441093843296128998604121485 165410191236048374476545557)
          ·
            refine ⟨7753602714189767553588073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165410191236048374476545557 7753602714189767553588073)
            ·
              refine ⟨5815202035642325665191055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753602714189767553588073 5815202035642325665191055)
              ·
                refine ⟨8722803053463488497786583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815202035642325665191055 8722803053463488497786583)
                ·
                  refine ⟨13084204580195232746679875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722803053463488497786583 13084204580195232746679875)
                  ·
                    refine ⟨19626306870292849120019813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13084204580195232746679875 19626306870292849120019813)
                    ·
                      refine ⟨3679932538179909210003715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19626306870292849120019813 3679932538179909210003715)
                      ·
                        rfl

theorem cell23_7166643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 1, 4].length) (baseStart_7166643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166643 prefixEnd_7166643 := by exact prefixLift 7166643
  have htrace : WordTrace (prefixWord ++ tailWord_7166643) baseStart_7166643 baseEnd_7166643 := by
    simpa [prefixWord, tailWord_7166643, baseEnd_7166643] using wordTrace_append hprefix tailTrace_7166643
  have hstable : (prefixWord ++ tailWord_7166643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166643).length < 2 ^ (prefixWord ++ tailWord_7166643).sum := by decide
  have hdescent : baseEnd_7166643 < baseStart_7166643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166653 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_7166653 : Nat := 118140960795 + 7166653 * 2 ^ 59
def prefixEnd_7166653 : Nat := 4983230072969 + 3 ^ 40 * 7166653 * 2
def baseEnd_7166653 : Nat := 1226645890995484723626223

theorem tailTrace_7166653 : CollatzResearch.WordTrace tailWord_7166653 prefixEnd_7166653 1226645890995484723626223 := by
  unfold tailWord_7166653
  simp only [CollatzResearch.WordTrace]
  refine ⟨261389308905447622732528613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174259539270298415155019075 261389308905447622732528613)
  ·
    refine ⟨49010495419771429262349115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261389308905447622732528613 49010495419771429262349115)
    ·
      refine ⟨73515743129657143893523673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49010495419771429262349115 73515743129657143893523673)
      ·
        refine ⟨55136807347242857920142755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73515743129657143893523673 55136807347242857920142755)
        ·
          refine ⟨82705211020864286880214133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55136807347242857920142755 82705211020864286880214133)
          ·
            refine ⟨7753613533206026895020075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82705211020864286880214133 7753613533206026895020075)
            ·
              refine ⟨11630420299809040342530113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753613533206026895020075 11630420299809040342530113)
              ·
                refine ⟨8722815224856780256897585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11630420299809040342530113 8722815224856780256897585)
                ·
                  refine ⟨6542111418642585192673189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8722815224856780256897585 6542111418642585192673189)
                  ·
                    refine ⟨1226645890995484723626223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542111418642585192673189 1226645890995484723626223)
                    ·
                      rfl

theorem cell23_7166653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_7166653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166653 prefixEnd_7166653 := by exact prefixLift 7166653
  have htrace : WordTrace (prefixWord ++ tailWord_7166653) baseStart_7166653 baseEnd_7166653 := by
    simpa [prefixWord, tailWord_7166653, baseEnd_7166653] using wordTrace_append hprefix tailTrace_7166653
  have hstable : (prefixWord ++ tailWord_7166653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166653).length < 2 ^ (prefixWord ++ tailWord_7166653).sum := by decide
  have hdescent : baseEnd_7166653 < baseStart_7166653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166660 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7166660 : Nat := 118140960795 + 7166660 * 2 ^ 59
def prefixEnd_7166660 : Nat := 4983230072969 + 3 ^ 40 * 7166660 * 2
def baseEnd_7166660 : Nat := 3679941267351035643491137

theorem tailTrace_7166660 : CollatzResearch.WordTrace tailWord_7166660 prefixEnd_7166660 3679941267351035643491137 := by
  unfold tailWord_7166660
  simp only [CollatzResearch.WordTrace]
  refine ⟨130694782108211131464016717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174259709477614841952022289 130694782108211131464016717)
  ·
    refine ⟨49010543290579174299006269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130694782108211131464016717 49010543290579174299006269)
    ·
      refine ⟨18378953733967190362127351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49010543290579174299006269 18378953733967190362127351)
      ·
        refine ⟨27568430600950785543191027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378953733967190362127351 27568430600950785543191027)
        ·
          refine ⟨41352645901426178314786541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27568430600950785543191027 41352645901426178314786541)
          ·
            refine ⟨15507242213034816868044953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41352645901426178314786541 15507242213034816868044953)
            ·
              refine ⟨11630431659776112651033715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15507242213034816868044953 11630431659776112651033715)
              ·
                refine ⟨17445647489664168976550573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630431659776112651033715 17445647489664168976550573)
                ·
                  refine ⟨6542117808624063366206465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17445647489664168976550573 6542117808624063366206465)
                  ·
                    refine ⟨4906588356468047524654849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542117808624063366206465 4906588356468047524654849)
                    ·
                      refine ⟨3679941267351035643491137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906588356468047524654849 3679941267351035643491137)
                      ·
                        rfl

theorem cell23_7166660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7166660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166660 prefixEnd_7166660 := by exact prefixLift 7166660
  have htrace : WordTrace (prefixWord ++ tailWord_7166660) baseStart_7166660 baseEnd_7166660 := by
    simpa [prefixWord, tailWord_7166660, baseEnd_7166660] using wordTrace_append hprefix tailTrace_7166660
  have hstable : (prefixWord ++ tailWord_7166660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166660).length < 2 ^ (prefixWord ++ tailWord_7166660).sum := by decide
  have hdescent : baseEnd_7166660 < baseStart_7166660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166689 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7166689 : Nat := 118140960795 + 7166689 * 2 ^ 59
def prefixEnd_7166689 : Nat := 4983230072969 + 3 ^ 40 * 7166689 * 2
def baseEnd_7166689 : Nat := 3679956158290016030028503

theorem tailTrace_7166689 : CollatzResearch.WordTrace tailWord_7166689 prefixEnd_7166689 3679956158290016030028503 := by
  unfold tailWord_7166689
  simp only [CollatzResearch.WordTrace]
  refine ⟨261390621933317200880839121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174260414622211467253892747 261390621933317200880839121)
  ·
    refine ⟨196042966449987900660629341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261390621933317200880839121 196042966449987900660629341)
    ·
      refine ⟨73516112418745462747736003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196042966449987900660629341 73516112418745462747736003)
      ·
        refine ⟨110274168628118194121604005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73516112418745462747736003 110274168628118194121604005)
        ·
          refine ⟨20676406617772161397800751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110274168628118194121604005 20676406617772161397800751)
          ·
            refine ⟨31014609926658242096701127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20676406617772161397800751 31014609926658242096701127)
            ·
              refine ⟨46521914889987363145051691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31014609926658242096701127 46521914889987363145051691)
              ·
                refine ⟨69782872334981044717577537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46521914889987363145051691 69782872334981044717577537)
                ·
                  refine ⟨52337154251235783538183153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69782872334981044717577537 52337154251235783538183153)
                  ·
                    refine ⟨39252865688426837653637365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52337154251235783538183153 39252865688426837653637365)
                    ·
                      refine ⟨3679956158290016030028503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39252865688426837653637365 3679956158290016030028503)
                      ·
                        rfl

theorem cell23_7166689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7166689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166689 prefixEnd_7166689 := by exact prefixLift 7166689
  have htrace : WordTrace (prefixWord ++ tailWord_7166689) baseStart_7166689 baseEnd_7166689 := by
    simpa [prefixWord, tailWord_7166689, baseEnd_7166689] using wordTrace_append hprefix tailTrace_7166689
  have hstable : (prefixWord ++ tailWord_7166689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166689).length < 2 ^ (prefixWord ++ tailWord_7166689).sum := by decide
  have hdescent : baseEnd_7166689 < baseStart_7166689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166703 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 1, 3, 2]
def baseStart_7166703 : Nat := 118140960795 + 7166703 * 2 ^ 59
def prefixEnd_7166703 : Nat := 4983230072969 + 3 ^ 40 * 7166703 * 2
def baseEnd_7166703 : Nat := 3679963347019178975253439

theorem tailTrace_7166703 : CollatzResearch.WordTrace tailWord_7166703 prefixEnd_7166703 3679963347019178975253439 := by
  unfold tailWord_7166703
  simp only [CollatzResearch.WordTrace]
  refine ⟨261391132555266481271848763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174260755036844320847899175 261391132555266481271848763)
  ·
    refine ⟨392086698832899721907773145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261391132555266481271848763 392086698832899721907773145)
    ·
      refine ⟨294065024124674791430829859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392086698832899721907773145 294065024124674791430829859)
      ·
        refine ⟨441097536187012187146244789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294065024124674791430829859 441097536187012187146244789)
        ·
          refine ⟨41352894017532392544960449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 441097536187012187146244789 41352894017532392544960449)
          ·
            refine ⟨31014670513149294408720337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41352894017532392544960449 31014670513149294408720337)
            ·
              refine ⟨23261002884861970806540253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31014670513149294408720337 23261002884861970806540253)
              ·
                refine ⟨8722876081823239052452595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23261002884861970806540253 8722876081823239052452595)
                ·
                  refine ⟨13084314122734858578678893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722876081823239052452595 13084314122734858578678893)
                  ·
                    refine ⟨4906617796025571967004585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13084314122734858578678893 4906617796025571967004585)
                    ·
                      refine ⟨3679963347019178975253439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906617796025571967004585 3679963347019178975253439)
                      ·
                        rfl

theorem cell23_7166703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3, 2].length) (baseStart_7166703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166703 prefixEnd_7166703 := by exact prefixLift 7166703
  have htrace : WordTrace (prefixWord ++ tailWord_7166703) baseStart_7166703 baseEnd_7166703 := by
    simpa [prefixWord, tailWord_7166703, baseEnd_7166703] using wordTrace_append hprefix tailTrace_7166703
  have hstable : (prefixWord ++ tailWord_7166703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166703).length < 2 ^ (prefixWord ++ tailWord_7166703).sum := by decide
  have hdescent : baseEnd_7166703 < baseStart_7166703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166719 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_7166719 : Nat := 118140960795 + 7166719 * 2 ^ 59
def prefixEnd_7166719 : Nat := 4983230072969 + 3 ^ 40 * 7166719 * 2
def baseEnd_7166719 : Nat := 3679971562709650912653365

theorem tailTrace_7166719 : CollatzResearch.WordTrace tailWord_7166719 prefixEnd_7166719 3679971562709650912653365 := by
  unfold tailWord_7166719
  simp only [CollatzResearch.WordTrace]
  refine ⟨261391716123208516004431211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174261144082139010669620807 261391716123208516004431211)
  ·
    refine ⟨392087574184812774006646817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261391716123208516004431211 392087574184812774006646817)
    ·
      refine ⟨294065680638609580504985113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392087574184812774006646817 294065680638609580504985113)
      ·
        refine ⟨220549260478957185378738835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294065680638609580504985113 220549260478957185378738835)
        ·
          refine ⟨330823890718435778068108253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220549260478957185378738835 330823890718435778068108253)
          ·
            refine ⟨124058959019413416775540595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330823890718435778068108253 124058959019413416775540595)
            ·
              refine ⟨186088438529120125163310893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124058959019413416775540595 186088438529120125163310893)
              ·
                refine ⟨69783164448420046936241585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186088438529120125163310893 69783164448420046936241585)
                ·
                  refine ⟨52337373336315035202181189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69783164448420046936241585 52337373336315035202181189)
                  ·
                    refine ⟨9813257500559069100408973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52337373336315035202181189 9813257500559069100408973)
                    ·
                      refine ⟨3679971562709650912653365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813257500559069100408973 3679971562709650912653365)
                      ·
                        rfl

theorem cell23_7166719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_7166719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166719 prefixEnd_7166719 := by exact prefixLift 7166719
  have htrace : WordTrace (prefixWord ++ tailWord_7166719) baseStart_7166719 baseEnd_7166719 := by
    simpa [prefixWord, tailWord_7166719, baseEnd_7166719] using wordTrace_append hprefix tailTrace_7166719
  have hstable : (prefixWord ++ tailWord_7166719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166719).length < 2 ^ (prefixWord ++ tailWord_7166719).sum := by decide
  have hdescent : baseEnd_7166719 < baseStart_7166719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166727 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7166727 : Nat := 118140960795 + 7166727 * 2 ^ 59
def prefixEnd_7166727 : Nat := 4983230072969 + 3 ^ 40 * 7166727 * 2
def baseEnd_7166727 : Nat := 3679975670554886881353329

theorem tailTrace_7166727 : CollatzResearch.WordTrace tailWord_7166727 prefixEnd_7166727 3679975670554886881353329 := by
  unfold tailWord_7166727
  simp only [CollatzResearch.WordTrace]
  refine ⟨261392007907179533370722435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174261338604786355580481623 261392007907179533370722435)
  ·
    refine ⟨392088011860769300056083653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261392007907179533370722435 392088011860769300056083653)
    ·
      refine ⟨73516502223894243760515685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392088011860769300056083653 73516502223894243760515685)
      ·
        refine ⟨13784344166980170705096691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73516502223894243760515685 13784344166980170705096691)
        ·
          refine ⟨20676516250470256057645037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13784344166980170705096691 20676516250470256057645037)
          ·
            refine ⟨7753693593926346021616889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20676516250470256057645037 7753693593926346021616889)
            ·
              refine ⟨5815270195444759516212667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753693593926346021616889 5815270195444759516212667)
              ·
                refine ⟨8722905293167139274319001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815270195444759516212667 8722905293167139274319001)
                ·
                  refine ⟨6542178969875354455739251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8722905293167139274319001 6542178969875354455739251)
                  ·
                    refine ⟨9813268454813031683608877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542178969875354455739251 9813268454813031683608877)
                    ·
                      refine ⟨3679975670554886881353329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813268454813031683608877 3679975670554886881353329)
                      ·
                        rfl

theorem cell23_7166727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7166727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166727 prefixEnd_7166727 := by exact prefixLift 7166727
  have htrace : WordTrace (prefixWord ++ tailWord_7166727) baseStart_7166727 baseEnd_7166727 := by
    simpa [prefixWord, tailWord_7166727, baseEnd_7166727] using wordTrace_append hprefix tailTrace_7166727
  have hstable : (prefixWord ++ tailWord_7166727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166727).length < 2 ^ (prefixWord ++ tailWord_7166727).sum := by decide
  have hdescent : baseEnd_7166727 < baseStart_7166727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166729 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_7166729 : Nat := 118140960795 + 7166729 * 2 ^ 59
def prefixEnd_7166729 : Nat := 4983230072969 + 3 ^ 40 * 7166729 * 2
def baseEnd_7166729 : Nat := 3679976697516195873528319

theorem tailTrace_7166729 : CollatzResearch.WordTrace tailWord_7166729 prefixEnd_7166729 3679976697516195873528319 := by
  unfold tailWord_7166729
  simp only [CollatzResearch.WordTrace]
  refine ⟨261392080853172287712295241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174261387235448191808196827 261392080853172287712295241)
  ·
    refine ⟨196044060639879215784221431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261392080853172287712295241 196044060639879215784221431)
    ·
      refine ⟨294066090959818823676332147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196044060639879215784221431 294066090959818823676332147)
      ·
        refine ⟨441099136439728235514498221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294066090959818823676332147 441099136439728235514498221)
        ·
          refine ⟨165412176164898088317936833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441099136439728235514498221 165412176164898088317936833)
          ·
            refine ⟨124059132123673566238452625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165412176164898088317936833 124059132123673566238452625)
            ·
              refine ⟨93044349092755174678839469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124059132123673566238452625 93044349092755174678839469)
              ·
                refine ⟨34891630909783190504564801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93044349092755174678839469 34891630909783190504564801)
                ·
                  refine ⟨26168723182337392878423601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34891630909783190504564801 26168723182337392878423601)
                  ·
                    refine ⟨19626542386753044658817701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26168723182337392878423601 19626542386753044658817701)
                    ·
                      refine ⟨3679976697516195873528319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19626542386753044658817701 3679976697516195873528319)
                      ·
                        rfl

theorem cell23_7166729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_7166729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166729 prefixEnd_7166729 := by exact prefixLift 7166729
  have htrace : WordTrace (prefixWord ++ tailWord_7166729) baseStart_7166729 baseEnd_7166729 := by
    simpa [prefixWord, tailWord_7166729, baseEnd_7166729] using wordTrace_append hprefix tailTrace_7166729
  have hstable : (prefixWord ++ tailWord_7166729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166729).length < 2 ^ (prefixWord ++ tailWord_7166729).sum := by decide
  have hdescent : baseEnd_7166729 < baseStart_7166729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166773 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 5]
def baseStart_7166773 : Nat := 118140960795 + 7166773 * 2 ^ 59
def prefixEnd_7166773 : Nat := 4983230072969 + 3 ^ 40 * 7166773 * 2
def baseEnd_7166773 : Nat := 408888810073888189042013

theorem tailTrace_7166773 : CollatzResearch.WordTrace tailWord_7166773 prefixEnd_7166773 408888810073888189042013 := by
  unfold tailWord_7166773
  simp only [CollatzResearch.WordTrace]
  refine ⟨261393685665012883226896973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174262457110008588817931315 261393685665012883226896973)
  ·
    refine ⟨98022632124379831210086365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261393685665012883226896973 98022632124379831210086365)
    ·
      refine ⟨36758487046642436703782387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98022632124379831210086365 36758487046642436703782387)
      ·
        refine ⟨55137730569963655055673581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36758487046642436703782387 55137730569963655055673581)
        ·
          refine ⟨20676648963736370645877593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55137730569963655055673581 20676648963736370645877593)
          ·
            refine ⟨15507486722802277984408195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20676648963736370645877593 15507486722802277984408195)
            ·
              refine ⟨23261230084203416976612293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15507486722802277984408195 23261230084203416976612293)
              ·
                refine ⟨4361480640788140683114805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23261230084203416976612293 4361480640788140683114805)
                ·
                  refine ⟨408888810073888189042013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361480640788140683114805 408888810073888189042013)
                  ·
                    rfl

theorem cell23_7166773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_7166773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166773 prefixEnd_7166773 := by exact prefixLift 7166773
  have htrace : WordTrace (prefixWord ++ tailWord_7166773) baseStart_7166773 baseEnd_7166773 := by
    simpa [prefixWord, tailWord_7166773, baseEnd_7166773] using wordTrace_append hprefix tailTrace_7166773
  have hstable : (prefixWord ++ tailWord_7166773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166773).length < 2 ^ (prefixWord ++ tailWord_7166773).sum := by decide
  have hdescent : baseEnd_7166773 < baseStart_7166773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166776 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_7166776 : Nat := 118140960795 + 7166776 * 2 ^ 59
def prefixEnd_7166776 : Nat := 4983230072969 + 3 ^ 40 * 7166776 * 2
def baseEnd_7166776 : Nat := 3680000831106957189640603

theorem tailTrace_7166776 : CollatzResearch.WordTrace tailWord_7166776 prefixEnd_7166776 3680000831106957189640603 := by
  unfold tailWord_7166776
  simp only [CollatzResearch.WordTrace]
  refine ⟨130696897542001007369628091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174262530056001343159504121 130696897542001007369628091)
  ·
    refine ⟨196045346313001511054442137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130696897542001007369628091 196045346313001511054442137)
    ·
      refine ⟨147034009734751133290831603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196045346313001511054442137 147034009734751133290831603)
      ·
        refine ⟨220551014602126699936247405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147034009734751133290831603 220551014602126699936247405)
        ·
          refine ⟨82706630475797512476092777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220551014602126699936247405 82706630475797512476092777)
          ·
            refine ⟨62029972856848134357069583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82706630475797512476092777 62029972856848134357069583)
            ·
              refine ⟨93044959285272201535604375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62029972856848134357069583 93044959285272201535604375)
              ·
                refine ⟨139567438927908302303406563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93044959285272201535604375 139567438927908302303406563)
                ·
                  refine ⟨209351158391862453455109845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139567438927908302303406563 209351158391862453455109845)
                  ·
                    refine ⟨4906667774809276252854137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209351158391862453455109845 4906667774809276252854137)
                    ·
                      refine ⟨3680000831106957189640603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906667774809276252854137 3680000831106957189640603)
                      ·
                        rfl

theorem cell23_7166776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_7166776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166776 prefixEnd_7166776 := by exact prefixLift 7166776
  have htrace : WordTrace (prefixWord ++ tailWord_7166776) baseStart_7166776 baseEnd_7166776 := by
    simpa [prefixWord, tailWord_7166776, baseEnd_7166776] using wordTrace_append hprefix tailTrace_7166776
  have hstable : (prefixWord ++ tailWord_7166776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166776).length < 2 ^ (prefixWord ++ tailWord_7166776).sum := by decide
  have hdescent : baseEnd_7166776 < baseStart_7166776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166790 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_7166790 : Nat := 118140960795 + 7166790 * 2 ^ 59
def prefixEnd_7166790 : Nat := 4983230072969 + 3 ^ 40 * 7166790 * 2
def baseEnd_7166790 : Nat := 408889779981791126096171

theorem tailTrace_7166790 : CollatzResearch.WordTrace tailWord_7166790 prefixEnd_7166790 408889779981791126096171 := by
  unfold tailWord_7166790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168572053310977972820807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174262870470634196753510549 8168572053310977972820807)
  ·
    refine ⟨12252858079966466959231211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8168572053310977972820807 12252858079966466959231211)
    ·
      refine ⟨18379287119949700438846817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252858079966466959231211 18379287119949700438846817)
      ·
        refine ⟨13784465339962275329135113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18379287119949700438846817 13784465339962275329135113)
        ·
          refine ⟨10338349004971706496851335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13784465339962275329135113 10338349004971706496851335)
          ·
            refine ⟨15507523507457559745277003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338349004971706496851335 15507523507457559745277003)
            ·
              refine ⟨23261285261186339617915505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15507523507457559745277003 23261285261186339617915505)
              ·
                refine ⟨17445963945889754713436629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23261285261186339617915505 17445963945889754713436629)
                ·
                  refine ⟨408889779981791126096171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17445963945889754713436629 408889779981791126096171)
                  ·
                    rfl

theorem cell23_7166790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_7166790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166790 prefixEnd_7166790 := by exact prefixLift 7166790
  have htrace : WordTrace (prefixWord ++ tailWord_7166790) baseStart_7166790 baseEnd_7166790 := by
    simpa [prefixWord, tailWord_7166790, baseEnd_7166790] using wordTrace_append hprefix tailTrace_7166790
  have hstable : (prefixWord ++ tailWord_7166790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166790).length < 2 ^ (prefixWord ++ tailWord_7166790).sum := by decide
  have hdescent : baseEnd_7166790 < baseStart_7166790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166816 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_7166816 : Nat := 118140960795 + 7166816 * 2 ^ 59
def prefixEnd_7166816 : Nat := 4983230072969 + 3 ^ 40 * 7166816 * 2
def baseEnd_7166816 : Nat := 1226673790111045677713473

theorem tailTrace_7166816 : CollatzResearch.WordTrace tailWord_7166816 prefixEnd_7166816 1226673790111045677713473 := by
  unfold tailWord_7166816
  simp only [CollatzResearch.WordTrace]
  refine ⟨130697627001928550785356151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174263502669238067713808201 130697627001928550785356151)
  ·
    refine ⟨196046440502892826178034227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130697627001928550785356151 196046440502892826178034227)
    ·
      refine ⟨294069660754339239267051341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196046440502892826178034227 294069660754339239267051341)
      ·
        refine ⟨110276122782877214725144253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294069660754339239267051341 110276122782877214725144253)
        ·
          refine ⟨41353546043578955521929095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110276122782877214725144253 41353546043578955521929095)
          ·
            refine ⟨62030319065368433282893643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41353546043578955521929095 62030319065368433282893643)
            ·
              refine ⟨93045478598052649924340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62030319065368433282893643 93045478598052649924340465)
              ·
                refine ⟨69784108948539487443255349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93045478598052649924340465 69784108948539487443255349)
                ·
                  refine ⟨6542260213925576947805189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69784108948539487443255349 6542260213925576947805189)
                  ·
                    refine ⟨1226673790111045677713473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542260213925576947805189 1226673790111045677713473)
                    ·
                      rfl

theorem cell23_7166816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_7166816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166816 prefixEnd_7166816 := by exact prefixLift 7166816
  have htrace : WordTrace (prefixWord ++ tailWord_7166816) baseStart_7166816 baseEnd_7166816 := by
    simpa [prefixWord, tailWord_7166816, baseEnd_7166816] using wordTrace_append hprefix tailTrace_7166816
  have hstable : (prefixWord ++ tailWord_7166816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166816).length < 2 ^ (prefixWord ++ tailWord_7166816).sum := by decide
  have hdescent : baseEnd_7166816 < baseStart_7166816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166823 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_7166823 : Nat := 118140960795 + 7166823 * 2 ^ 59
def prefixEnd_7166823 : Nat := 4983230072969 + 3 ^ 40 * 7166823 * 2
def baseEnd_7166823 : Nat := 3680024964697718505752887

theorem tailTrace_7166823 : CollatzResearch.WordTrace tailWord_7166823 prefixEnd_7166823 3680024964697718505752887 := by
  unfold tailWord_7166823
  simp only [CollatzResearch.WordTrace]
  refine ⟨261395509314831741766217123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174263672876554494510811415 261395509314831741766217123)
  ·
    refine ⟨392093263972247612649325685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261395509314831741766217123 392093263972247612649325685)
    ·
      refine ⟨36758743497398213685874283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392093263972247612649325685 36758743497398213685874283)
      ·
        refine ⟨55138115246097320528811425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36758743497398213685874283 55138115246097320528811425)
        ·
          refine ⟨41353586434572990396608569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55138115246097320528811425 41353586434572990396608569)
          ·
            refine ⟨31015189825929742797456427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41353586434572990396608569 31015189825929742797456427)
            ·
              refine ⟨46522784738894614196184641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31015189825929742797456427 46522784738894614196184641)
              ·
                refine ⟨34892088554170960647138481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46522784738894614196184641 34892088554170960647138481)
                ·
                  refine ⟨26169066415628220485353861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34892088554170960647138481 26169066415628220485353861)
                  ·
                    refine ⟨4906699952930291341003849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26169066415628220485353861 4906699952930291341003849)
                    ·
                      refine ⟨3680024964697718505752887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906699952930291341003849 3680024964697718505752887)
                      ·
                        rfl

theorem cell23_7166823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_7166823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166823 prefixEnd_7166823 := by exact prefixLift 7166823
  have htrace : WordTrace (prefixWord ++ tailWord_7166823) baseStart_7166823 baseEnd_7166823 := by
    simpa [prefixWord, tailWord_7166823, baseEnd_7166823] using wordTrace_append hprefix tailTrace_7166823
  have hstable : (prefixWord ++ tailWord_7166823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166823).length < 2 ^ (prefixWord ++ tailWord_7166823).sum := by decide
  have hdescent : baseEnd_7166823 < baseStart_7166823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166833 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_7166833 : Nat := 118140960795 + 7166833 * 2 ^ 59
def prefixEnd_7166833 : Nat := 4983230072969 + 3 ^ 40 * 7166833 * 2
def baseEnd_7166833 : Nat := 1226676699834754488875947

theorem tailTrace_7166833 : CollatzResearch.WordTrace tailWord_7166833 prefixEnd_7166833 1226676699834754488875947 := by
  unfold tailWord_7166833
  simp only [CollatzResearch.WordTrace]
  refine ⟨261395874044795513474081153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174263916029863675649387435 261395874044795513474081153)
  ·
    refine ⟨196046905533596635105560865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261395874044795513474081153 196046905533596635105560865)
    ·
      refine ⟨147035179150197476329170649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196046905533596635105560865 147035179150197476329170649)
      ·
        refine ⟨110276384362648107246877987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147035179150197476329170649 110276384362648107246877987)
        ·
          refine ⟨165414576543972160870316981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110276384362648107246877987 165414576543972160870316981)
          ·
            refine ⟨15507616550997390081592217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165414576543972160870316981 15507616550997390081592217)
            ·
              refine ⟨11630712413248042561194163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15507616550997390081592217 11630712413248042561194163)
              ·
                refine ⟨17446068619872063841791245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630712413248042561194163 17446068619872063841791245)
                ·
                  refine ⟨6542275732452023940671717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17446068619872063841791245 6542275732452023940671717)
                  ·
                    refine ⟨1226676699834754488875947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542275732452023940671717 1226676699834754488875947)
                    ·
                      rfl

theorem cell23_7166833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_7166833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166833 prefixEnd_7166833 := by exact prefixLift 7166833
  have htrace : WordTrace (prefixWord ++ tailWord_7166833) baseStart_7166833 baseEnd_7166833 := by
    simpa [prefixWord, tailWord_7166833, baseEnd_7166833] using wordTrace_append hprefix tailTrace_7166833
  have hstable : (prefixWord ++ tailWord_7166833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166833).length < 2 ^ (prefixWord ++ tailWord_7166833).sum := by decide
  have hdescent : baseEnd_7166833 < baseStart_7166833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166883 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 4, 3, 2]
def baseStart_7166883 : Nat := 118140960795 + 7166883 * 2 ^ 59
def prefixEnd_7166883 : Nat := 4983230072969 + 3 ^ 40 * 7166883 * 2
def baseEnd_7166883 : Nat := 3680055773536988271002611

theorem tailTrace_7166883 : CollatzResearch.WordTrace tailWord_7166883 prefixEnd_7166883 3680055773536988271002611 := by
  unfold tailWord_7166883
  simp only [CollatzResearch.WordTrace]
  refine ⟨261397697694614372013401303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174265131796409581342267535 261397697694614372013401303)
  ·
    refine ⟨392096546541921558020101955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261397697694614372013401303 392096546541921558020101955)
    ·
      refine ⟨588144819812882337030152933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392096546541921558020101955 588144819812882337030152933)
      ·
        refine ⟨110277153714915438193153675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588144819812882337030152933 110277153714915438193153675)
        ·
          refine ⟨165415730572373157289730513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110277153714915438193153675 165415730572373157289730513)
          ·
            refine ⟨124061797929279867967297885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165415730572373157289730513 124061797929279867967297885)
            ·
              refine ⟨46523174223479950487736707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124061797929279867967297885 46523174223479950487736707)
              ·
                refine ⟨69784761335219925731605061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46523174223479950487736707 69784761335219925731605061)
                ·
                  refine ⟨13084642750353736074675949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69784761335219925731605061 13084642750353736074675949)
                  ·
                    refine ⟨4906741031382651028003481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13084642750353736074675949 4906741031382651028003481)
                    ·
                      refine ⟨3680055773536988271002611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906741031382651028003481 3680055773536988271002611)
                      ·
                        rfl

theorem cell23_7166883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_7166883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166883 prefixEnd_7166883 := by exact prefixLift 7166883
  have htrace : WordTrace (prefixWord ++ tailWord_7166883) baseStart_7166883 baseEnd_7166883 := by
    simpa [prefixWord, tailWord_7166883, baseEnd_7166883] using wordTrace_append hprefix tailTrace_7166883
  have hstable : (prefixWord ++ tailWord_7166883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166883).length < 2 ^ (prefixWord ++ tailWord_7166883).sum := by decide
  have hdescent : baseEnd_7166883 < baseStart_7166883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166897 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 6]
def baseStart_7166897 : Nat := 118140960795 + 7166897 * 2 ^ 59
def prefixEnd_7166897 : Nat := 4983230072969 + 3 ^ 40 * 7166897 * 2
def baseEnd_7166897 : Nat := 408895884696239024025283

theorem tailTrace_7166897 : CollatzResearch.WordTrace tailWord_7166897 prefixEnd_7166897 408895884696239024025283 := by
  unfold tailWord_7166897
  simp only [CollatzResearch.WordTrace]
  refine ⟨261398208316563652404410945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174265472211042434936273963 261398208316563652404410945)
  ·
    refine ⟨196048656237422739303308209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261398208316563652404410945 196048656237422739303308209)
    ·
      refine ⟨147036492178067054477481157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196048656237422739303308209 147036492178067054477481157)
      ·
        refine ⟨27569342283387572714527717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147036492178067054477481157 27569342283387572714527717)
        ·
          refine ⟨5169251678135169883973947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27569342283387572714527717 5169251678135169883973947)
          ·
            refine ⟨7753877517202754825960921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169251678135169883973947 7753877517202754825960921)
            ·
              refine ⟨5815408137902066119470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753877517202754825960921 5815408137902066119470691)
              ·
                refine ⟨8723112206853099179206037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815408137902066119470691 8723112206853099179206037)
                ·
                  refine ⟨408895884696239024025283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8723112206853099179206037 408895884696239024025283)
                  ·
                    rfl

theorem cell23_7166897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_7166897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166897 prefixEnd_7166897 := by exact prefixLift 7166897
  have htrace : WordTrace (prefixWord ++ tailWord_7166897) baseStart_7166897 baseEnd_7166897 := by
    simpa [prefixWord, tailWord_7166897, baseEnd_7166897] using wordTrace_append hprefix tailTrace_7166897
  have hstable : (prefixWord ++ tailWord_7166897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166897).length < 2 ^ (prefixWord ++ tailWord_7166897).sum := by decide
  have hdescent : baseEnd_7166897 < baseStart_7166897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166906 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_7166906 : Nat := 118140960795 + 7166906 * 2 ^ 59
def prefixEnd_7166906 : Nat := 4983230072969 + 3 ^ 40 * 7166906 * 2
def baseEnd_7166906 : Nat := 1226689194530680560338335

theorem tailTrace_7166906 : CollatzResearch.WordTrace tailWord_7166906 prefixEnd_7166906 1226689194530680560338335 := by
  unfold tailWord_7166906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65349634143382761735372143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174265691049020697960992381 65349634143382761735372143)
  ·
    refine ⟨98024451215074142603058215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65349634143382761735372143 98024451215074142603058215)
    ·
      refine ⟨147036676822611213904587323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98024451215074142603058215 147036676822611213904587323)
      ·
        refine ⟨220555015233916820856880985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147036676822611213904587323 220555015233916820856880985)
        ·
          refine ⟨165416261425437615642660739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220555015233916820856880985 165416261425437615642660739)
          ·
            refine ⟨248124392138156423463991109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165416261425437615642660739 248124392138156423463991109)
            ·
              refine ⟨46523323525904329399498333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248124392138156423463991109 46523323525904329399498333)
              ·
                refine ⟨17446246322214123524811875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46523323525904329399498333 17446246322214123524811875)
                ·
                  refine ⟨26169369483321185287217813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17446246322214123524811875 26169369483321185287217813)
                  ·
                    refine ⟨1226689194530680560338335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26169369483321185287217813 1226689194530680560338335)
                    ·
                      rfl

theorem cell23_7166906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_7166906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166906 prefixEnd_7166906 := by exact prefixLift 7166906
  have htrace : WordTrace (prefixWord ++ tailWord_7166906) baseStart_7166906 baseEnd_7166906 := by
    simpa [prefixWord, tailWord_7166906, baseEnd_7166906] using wordTrace_append hprefix tailTrace_7166906
  have hstable : (prefixWord ++ tailWord_7166906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166906).length < 2 ^ (prefixWord ++ tailWord_7166906).sum := by decide
  have hdescent : baseEnd_7166906 < baseStart_7166906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166941 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_7166941 : Nat := 118140960795 + 7166941 * 2 ^ 59
def prefixEnd_7166941 : Nat := 4983230072969 + 3 ^ 40 * 7166941 * 2
def baseEnd_7166941 : Nat := 3680085555414949044077345

theorem tailTrace_7166941 : CollatzResearch.WordTrace tailWord_7166941 prefixEnd_7166941 3680085555414949044077345 := by
  unfold tailWord_7166941
  simp only [CollatzResearch.WordTrace]
  refine ⟨261399813128404247919012677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174266542085602831946008451 261399813128404247919012677)
  ·
    refine ⟨49012464961575796484814877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261399813128404247919012677 49012464961575796484814877)
    ·
      refine ⟨18379674360590923681805579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49012464961575796484814877 18379674360590923681805579)
      ·
        refine ⟨27569511540886385522708369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18379674360590923681805579 27569511540886385522708369)
        ·
          refine ⟨20677133655664789142031277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569511540886385522708369 20677133655664789142031277)
          ·
            refine ⟨7753925120874295928261729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20677133655664789142031277 7753925120874295928261729)
            ·
              refine ⟨5815443840655721946196297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753925120874295928261729 5815443840655721946196297)
              ·
                refine ⟨4361582880491791459647223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815443840655721946196297 4361582880491791459647223)
                ·
                  refine ⟨6542374320737687189470835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361582880491791459647223 6542374320737687189470835)
                  ·
                    refine ⟨9813561481106530784206253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542374320737687189470835 9813561481106530784206253)
                    ·
                      refine ⟨3680085555414949044077345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813561481106530784206253 3680085555414949044077345)
                      ·
                        rfl

theorem cell23_7166941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_7166941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166941 prefixEnd_7166941 := by exact prefixLift 7166941
  have htrace : WordTrace (prefixWord ++ tailWord_7166941) baseStart_7166941 baseEnd_7166941 := by
    simpa [prefixWord, tailWord_7166941, baseEnd_7166941] using wordTrace_append hprefix tailTrace_7166941
  have hstable : (prefixWord ++ tailWord_7166941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166941).length < 2 ^ (prefixWord ++ tailWord_7166941).sum := by decide
  have hdescent : baseEnd_7166941 < baseStart_7166941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166963 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 3]
def baseStart_7166963 : Nat := 118140960795 + 7166963 * 2 ^ 59
def prefixEnd_7166963 : Nat := 4983230072969 + 3 ^ 40 * 7166963 * 2
def baseEnd_7166963 : Nat := 3680096851989347958002243

theorem tailTrace_7166963 : CollatzResearch.WordTrace tailWord_7166963 prefixEnd_7166963 3680096851989347958002243 := by
  unfold tailWord_7166963
  simp only [CollatzResearch.WordTrace]
  refine ⟨261400615534324545676313543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174267077022883030450875695 261400615534324545676313543)
  ·
    refine ⟨392100923301486818514470315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261400615534324545676313543 392100923301486818514470315)
    ·
      refine ⟨588151384952230227771705473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392100923301486818514470315 588151384952230227771705473)
      ·
        refine ⟨441113538714172670828779105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588151384952230227771705473 441113538714172670828779105)
        ·
          refine ⟨330835154035629503121584329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441113538714172670828779105 330835154035629503121584329)
          ·
            refine ⟨248126365526722127341188247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330835154035629503121584329 248126365526722127341188247)
            ·
              refine ⟨372189548290083191011782371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248126365526722127341188247 372189548290083191011782371)
              ·
                refine ⟨558284322435124786517673557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372189548290083191011782371 558284322435124786517673557)
                ·
                  refine ⟨6542394403536618592003987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 558284322435124786517673557 6542394403536618592003987)
                  ·
                    refine ⟨9813591605304927888005981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542394403536618592003987 9813591605304927888005981)
                    ·
                      refine ⟨3680096851989347958002243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813591605304927888005981 3680096851989347958002243)
                      ·
                        rfl

theorem cell23_7166963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_7166963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166963 prefixEnd_7166963 := by exact prefixLift 7166963
  have htrace : WordTrace (prefixWord ++ tailWord_7166963) baseStart_7166963 baseEnd_7166963 := by
    simpa [prefixWord, tailWord_7166963, baseEnd_7166963] using wordTrace_append hprefix tailTrace_7166963
  have hstable : (prefixWord ++ tailWord_7166963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166963).length < 2 ^ (prefixWord ++ tailWord_7166963).sum := by decide
  have hdescent : baseEnd_7166963 < baseStart_7166963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7166997 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_7166997 : Nat := 118140960795 + 7166997 * 2 ^ 59
def prefixEnd_7166997 : Nat := 4983230072969 + 3 ^ 40 * 7166997 * 2
def baseEnd_7166997 : Nat := 3680114310331600824977087

theorem tailTrace_7166997 : CollatzResearch.WordTrace tailWord_7166997 prefixEnd_7166997 3680114310331600824977087 := by
  unfold tailWord_7166997
  simp only [CollatzResearch.WordTrace]
  refine ⟨261401855616201369483051245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174267903744134246322034163 261401855616201369483051245)
  ·
    refine ⟨98025695856075513556144217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261401855616201369483051245 98025695856075513556144217)
    ·
      refine ⟨73519271892056635167108163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98025695856075513556144217 73519271892056635167108163)
      ·
        refine ⟨110278907838084952750662245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73519271892056635167108163 110278907838084952750662245)
        ·
          refine ⟨20677295219640928640749171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110278907838084952750662245 20677295219640928640749171)
          ·
            refine ⟨31015942829461392961123757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20677295219640928640749171 31015942829461392961123757)
            ·
              refine ⟨11630978561048022360421409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31015942829461392961123757 11630978561048022360421409)
              ·
                refine ⟨8723233920786016770316057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11630978561048022360421409 8723233920786016770316057)
                ·
                  refine ⟨6542425440589512577737043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723233920786016770316057 6542425440589512577737043)
                  ·
                    refine ⟨9813638160884268866605565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542425440589512577737043 9813638160884268866605565)
                    ·
                      refine ⟨3680114310331600824977087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813638160884268866605565 3680114310331600824977087)
                      ·
                        rfl

theorem cell23_7166997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_7166997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7166997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7166997 prefixEnd_7166997 := by exact prefixLift 7166997
  have htrace : WordTrace (prefixWord ++ tailWord_7166997) baseStart_7166997 baseEnd_7166997 := by
    simpa [prefixWord, tailWord_7166997, baseEnd_7166997] using wordTrace_append hprefix tailTrace_7166997
  have hstable : (prefixWord ++ tailWord_7166997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7166997).length < 2 ^ (prefixWord ++ tailWord_7166997).sum := by decide
  have hdescent : baseEnd_7166997 < baseStart_7166997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7166997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167037 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7167037 : Nat := 118140960795 + 7167037 * 2 ^ 59
def prefixEnd_7167037 : Nat := 4983230072969 + 3 ^ 40 * 7167037 * 2
def baseEnd_7167037 : Nat := 3680134849557780668476903

theorem tailTrace_7167037 : CollatzResearch.WordTrace tailWord_7167037 prefixEnd_7167037 3680134849557780668476903 := by
  unfold tailWord_7167037
  simp only [CollatzResearch.WordTrace]
  refine ⟨261403314536056456314507365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174268876357370970876338243 261403314536056456314507365)
  ·
    refine ⟨49013121475510585558970131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261403314536056456314507365 49013121475510585558970131)
    ·
      refine ⟨73519682213265878338455197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49013121475510585558970131 73519682213265878338455197)
      ·
        refine ⟨27569880829974704376920699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73519682213265878338455197 27569880829974704376920699)
        ·
          refine ⟨41354821244962056565381049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27569880829974704376920699 41354821244962056565381049)
          ·
            refine ⟨31016115933721542424035787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41354821244962056565381049 31016115933721542424035787)
            ·
              refine ⟨46524173900582313636053681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31016115933721542424035787 46524173900582313636053681)
              ·
                refine ⟨34893130425436735227040261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46524173900582313636053681 34893130425436735227040261)
                ·
                  refine ⟨6542461954769387855070049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34893130425436735227040261 6542461954769387855070049)
                  ·
                    refine ⟨4906846466077040891302537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542461954769387855070049 4906846466077040891302537)
                    ·
                      refine ⟨3680134849557780668476903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906846466077040891302537 3680134849557780668476903)
                      ·
                        rfl

theorem cell23_7167037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7167037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167037 prefixEnd_7167037 := by exact prefixLift 7167037
  have htrace : WordTrace (prefixWord ++ tailWord_7167037) baseStart_7167037 baseEnd_7167037 := by
    simpa [prefixWord, tailWord_7167037, baseEnd_7167037] using wordTrace_append hprefix tailTrace_7167037
  have hstable : (prefixWord ++ tailWord_7167037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167037).length < 2 ^ (prefixWord ++ tailWord_7167037).sum := by decide
  have hdescent : baseEnd_7167037 < baseStart_7167037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167060 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 5]
def baseStart_7167060 : Nat := 118140960795 + 7167060 * 2 ^ 59
def prefixEnd_7167060 : Nat := 4983230072969 + 3 ^ 40 * 7167060 * 2
def baseEnd_7167060 : Nat := 408905184401426008721033

theorem tailTrace_7167060 : CollatzResearch.WordTrace tailWord_7167060 prefixEnd_7167060 408905184401426008721033 := by
  unfold tailWord_7167060
  simp only [CollatzResearch.WordTrace]
  refine ⟨130702076707486565621297317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174269435609982087495063089 130702076707486565621297317)
  ·
    refine ⟨24506639382653731053993247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130702076707486565621297317 24506639382653731053993247)
    ·
      refine ⟨36759959073980596580989871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24506639382653731053993247 36759959073980596580989871)
      ·
        refine ⟨55139938610970894871484807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36759959073980596580989871 55139938610970894871484807)
        ·
          refine ⟨82709907916456342307227211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55139938610970894871484807 82709907916456342307227211)
          ·
            refine ⟨124064861874684513460840817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82709907916456342307227211 124064861874684513460840817)
            ·
              refine ⟨93048646406013385095630613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124064861874684513460840817 93048646406013385095630613)
              ·
                refine ⟨4361655300281877426357685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93048646406013385095630613 4361655300281877426357685)
                ·
                  refine ⟨408905184401426008721033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361655300281877426357685 408905184401426008721033)
                  ·
                    rfl

theorem cell23_7167060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_7167060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167060 prefixEnd_7167060 := by exact prefixLift 7167060
  have htrace : WordTrace (prefixWord ++ tailWord_7167060) baseStart_7167060 baseEnd_7167060 := by
    simpa [prefixWord, tailWord_7167060, baseEnd_7167060] using wordTrace_append hprefix tailTrace_7167060
  have hstable : (prefixWord ++ tailWord_7167060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167060).length < 2 ^ (prefixWord ++ tailWord_7167060).sum := by decide
  have hdescent : baseEnd_7167060 < baseStart_7167060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167090 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_7167090 : Nat := 118140960795 + 7167090 * 2 ^ 59
def prefixEnd_7167090 : Nat := 4983230072969 + 3 ^ 40 * 7167090 * 2
def baseEnd_7167090 : Nat := 1226720688010822987038053

theorem tailTrace_7167090 : CollatzResearch.WordTrace tailWord_7167090 prefixEnd_7167090 1226720688010822987038053 := by
  unfold tailWord_7167090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65351311901216111591546681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174270165069909630910791149 65351311901216111591546681)
  ·
    refine ⟨49013483925912083693660011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65351311901216111591546681 49013483925912083693660011)
    ·
      refine ⟨73520225888868125540490017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49013483925912083693660011 73520225888868125540490017)
      ·
        refine ⟨55140169416651094155367513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73520225888868125540490017 55140169416651094155367513)
        ·
          refine ⟨41355127062488320616525635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55140169416651094155367513 41355127062488320616525635)
          ·
            refine ⟨62032690593732480924788453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41355127062488320616525635 62032690593732480924788453)
            ·
              refine ⟨11631129486324840173397835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62032690593732480924788453 11631129486324840173397835)
              ·
                refine ⟨17446694229487260260096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11631129486324840173397835 17446694229487260260096753)
                ·
                  refine ⟨13085020672115445195072565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17446694229487260260096753 13085020672115445195072565)
                  ·
                    refine ⟨1226720688010822987038053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13085020672115445195072565 1226720688010822987038053)
                    ·
                      rfl

theorem cell23_7167090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_7167090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167090 prefixEnd_7167090 := by exact prefixLift 7167090
  have htrace : WordTrace (prefixWord ++ tailWord_7167090) baseStart_7167090 baseEnd_7167090 := by
    simpa [prefixWord, tailWord_7167090, baseEnd_7167090] using wordTrace_append hprefix tailTrace_7167090
  have hstable : (prefixWord ++ tailWord_7167090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167090).length < 2 ^ (prefixWord ++ tailWord_7167090).sum := by decide
  have hdescent : baseEnd_7167090 < baseStart_7167090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167127 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_7167127 : Nat := 118140960795 + 7167127 * 2 ^ 59
def prefixEnd_7167127 : Nat := 4983230072969 + 3 ^ 40 * 7167127 * 2
def baseEnd_7167127 : Nat := 3680181062816685316351489

theorem tailTrace_7167127 : CollatzResearch.WordTrace tailWord_7167127 prefixEnd_7167127 3680181062816685316351489 := by
  unfold tailWord_7167127
  simp only [CollatzResearch.WordTrace]
  refine ⟨261406597105730401685283635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174271064737153601123522423 261406597105730401685283635)
  ·
    refine ⟨392109895658595602527925453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261406597105730401685283635 392109895658595602527925453)
    ·
      refine ⟨147041210871973350947972045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392109895658595602527925453 147041210871973350947972045)
      ·
        refine ⟨55140454076990006605489517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147041210871973350947972045 55140454076990006605489517)
        ·
          refine ⟨20677670278871252477058569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55140454076990006605489517 20677670278871252477058569)
          ·
            refine ⟨15508252709153439357793927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20677670278871252477058569 15508252709153439357793927)
            ·
              refine ⟨23262379063730159036690891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15508252709153439357793927 23262379063730159036690891)
              ·
                refine ⟨34893568595595238555036337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23262379063730159036690891 34893568595595238555036337)
                ·
                  refine ⟨26170176446696428916277253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34893568595595238555036337 26170176446696428916277253)
                  ·
                    refine ⟨4906908083755580421801985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26170176446696428916277253 4906908083755580421801985)
                    ·
                      refine ⟨3680181062816685316351489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4906908083755580421801985 3680181062816685316351489)
                      ·
                        rfl

theorem cell23_7167127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_7167127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167127 prefixEnd_7167127 := by exact prefixLift 7167127
  have htrace : WordTrace (prefixWord ++ tailWord_7167127) baseStart_7167127 baseEnd_7167127 := by
    simpa [prefixWord, tailWord_7167127, baseEnd_7167127] using wordTrace_append hprefix tailTrace_7167127
  have hstable : (prefixWord ++ tailWord_7167127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167127).length < 2 ^ (prefixWord ++ tailWord_7167127).sum := by decide
  have hdescent : baseEnd_7167127 < baseStart_7167127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167154 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_7167154 : Nat := 118140960795 + 7167154 * 2 ^ 59
def prefixEnd_7167154 : Nat := 4983230072969 + 3 ^ 40 * 7167154 * 2
def baseEnd_7167154 : Nat := 1226731642264785570237955

theorem tailTrace_7167154 : CollatzResearch.WordTrace tailWord_7167154 prefixEnd_7167154 1226731642264785570237955 := by
  unfold tailWord_7167154
  simp only [CollatzResearch.WordTrace]
  refine ⟨65351895469158146324129129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174271721251088390197677677 65351895469158146324129129)
  ·
    refine ⟨49013921601868609743096847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65351895469158146324129129 49013921601868609743096847)
    ·
      refine ⟨73520882402802914614645271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49013921601868609743096847 73520882402802914614645271)
      ·
        refine ⟨110281323604204371921967907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73520882402802914614645271 110281323604204371921967907)
        ·
          refine ⟨165421985406306557882951861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110281323604204371921967907 165421985406306557882951861)
          ·
            refine ⟨15508311131841239801526737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165421985406306557882951861 15508311131841239801526737)
            ·
              refine ⟨11631233348880929851145053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15508311131841239801526737 11631233348880929851145053)
              ·
                refine ⟨4361712505830348694179395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11631233348880929851145053 4361712505830348694179395)
                ·
                  refine ⟨6542568758745523041269093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361712505830348694179395 6542568758745523041269093)
                  ·
                    refine ⟨1226731642264785570237955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542568758745523041269093 1226731642264785570237955)
                    ·
                      rfl

theorem cell23_7167154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_7167154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167154 prefixEnd_7167154 := by exact prefixLift 7167154
  have htrace : WordTrace (prefixWord ++ tailWord_7167154) baseStart_7167154 baseEnd_7167154 := by
    simpa [prefixWord, tailWord_7167154, baseEnd_7167154] using wordTrace_append hprefix tailTrace_7167154
  have hstable : (prefixWord ++ tailWord_7167154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167154).length < 2 ^ (prefixWord ++ tailWord_7167154).sum := by decide
  have hdescent : baseEnd_7167154 < baseStart_7167154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167163 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 5, 5]
def baseStart_7167163 : Nat := 118140960795 + 7167163 * 2 ^ 59
def prefixEnd_7167163 : Nat := 4983230072969 + 3 ^ 40 * 7167163 * 2
def baseEnd_7167163 : Nat := 1226733182706749058500441

theorem tailTrace_7167163 : CollatzResearch.WordTrace tailWord_7167163 prefixEnd_7167163 1226733182706749058500441 := by
  unfold tailWord_7167163
  simp only [CollatzResearch.WordTrace]
  refine ⟨261407910133599979833594143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174271940089066653222396095 261407910133599979833594143)
  ·
    refine ⟨392111865200399969750391215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261407910133599979833594143 392111865200399969750391215)
    ·
      refine ⟨588167797800599954625586823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392111865200399969750391215 588167797800599954625586823)
      ·
        refine ⟨882251696700899931938380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588167797800599954625586823 882251696700899931938380235)
        ·
          refine ⟨1323377545051349897907570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882251696700899931938380235 1323377545051349897907570353)
          ·
            refine ⟨992533158788512423430677765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323377545051349897907570353 992533158788512423430677765)
            ·
              refine ⟨186099967272846079393252081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 992533158788512423430677765 186099967272846079393252081)
              ·
                refine ⟨139574975454634559544939061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186099967272846079393252081 139574975454634559544939061)
                ·
                  refine ⟨13085153948871989957338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139574975454634559544939061 13085153948871989957338037)
                  ·
                    refine ⟨1226733182706749058500441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13085153948871989957338037 1226733182706749058500441)
                    ·
                      rfl

theorem cell23_7167163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].length) (baseStart_7167163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167163 prefixEnd_7167163 := by exact prefixLift 7167163
  have htrace : WordTrace (prefixWord ++ tailWord_7167163) baseStart_7167163 baseEnd_7167163 := by
    simpa [prefixWord, tailWord_7167163, baseEnd_7167163] using wordTrace_append hprefix tailTrace_7167163
  have hstable : (prefixWord ++ tailWord_7167163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167163).length < 2 ^ (prefixWord ++ tailWord_7167163).sum := by decide
  have hdescent : baseEnd_7167163 < baseStart_7167163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167183 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_7167183 : Nat := 118140960795 + 7167183 * 2 ^ 59
def prefixEnd_7167183 : Nat := 4983230072969 + 3 ^ 40 * 7167183 * 2
def baseEnd_7167183 : Nat := 3680209817733337097251231

theorem tailTrace_7167183 : CollatzResearch.WordTrace tailWord_7167183 prefixEnd_7167183 3680209817733337097251231 := by
  unfold tailWord_7167183
  simp only [CollatzResearch.WordTrace]
  refine ⟨261408639593527523249322203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174272426395685015499548135 261408639593527523249322203)
  ·
    refine ⟨392112959390291284873983305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261408639593527523249322203 392112959390291284873983305)
    ·
      refine ⟨294084719542718463655487479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392112959390291284873983305 294084719542718463655487479)
      ·
        refine ⟨441127079314077695483231219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294084719542718463655487479 441127079314077695483231219)
        ·
          refine ⟨661690618971116543224846829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441127079314077695483231219 661690618971116543224846829)
          ·
            refine ⟨248133982114168703709317561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661690618971116543224846829 248133982114168703709317561)
            ·
              refine ⟨186100486585626527781988171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248133982114168703709317561 186100486585626527781988171)
              ·
                refine ⟨279150729878439791672982257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186100486585626527781988171 279150729878439791672982257)
                ·
                  refine ⟨209363047408829843754736693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279150729878439791672982257 209363047408829843754736693)
                  ·
                    refine ⟨19627785694577797852006565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209363047408829843754736693 19627785694577797852006565)
                    ·
                      refine ⟨3680209817733337097251231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19627785694577797852006565 3680209817733337097251231)
                      ·
                        rfl

theorem cell23_7167183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_7167183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167183 prefixEnd_7167183 := by exact prefixLift 7167183
  have htrace : WordTrace (prefixWord ++ tailWord_7167183) baseStart_7167183 baseEnd_7167183 := by
    simpa [prefixWord, tailWord_7167183, baseEnd_7167183] using wordTrace_append hprefix tailTrace_7167183
  have hstable : (prefixWord ++ tailWord_7167183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167183).length < 2 ^ (prefixWord ++ tailWord_7167183).sum := by decide
  have hdescent : baseEnd_7167183 < baseStart_7167183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167211 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 1, 1, 3]
def baseStart_7167211 : Nat := 118140960795 + 7167211 * 2 ^ 59
def prefixEnd_7167211 : Nat := 4983230072969 + 3 ^ 40 * 7167211 * 2
def baseEnd_7167211 : Nat := 3680224195191662987701103

theorem tailTrace_7167211 : CollatzResearch.WordTrace tailWord_7167211 prefixEnd_7167211 3680224195191662987701103 := by
  unfold tailWord_7167211
  simp only [CollatzResearch.WordTrace]
  refine ⟨261409660837426084031341487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174273107224950722687560991 261409660837426084031341487)
  ·
    refine ⟨392114491256139126047012231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261409660837426084031341487 392114491256139126047012231)
    ·
      refine ⟨588171736884208689070518347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392114491256139126047012231 588171736884208689070518347)
      ·
        refine ⟨882257605326313033605777521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588171736884208689070518347 882257605326313033605777521)
        ·
          refine ⟨661693203994734775204333141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882257605326313033605777521 661693203994734775204333141)
          ·
            refine ⟨7754217234313298146925779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 661693203994734775204333141 7754217234313298146925779)
            ·
              refine ⟨11631325851469947220388669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754217234313298146925779 11631325851469947220388669)
              ·
                refine ⟨4361747194301230207645751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11631325851469947220388669 4361747194301230207645751)
                ·
                  refine ⟨6542620791451845311468627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361747194301230207645751 6542620791451845311468627)
                  ·
                    refine ⟨9813931187177767967202941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542620791451845311468627 9813931187177767967202941)
                    ·
                      refine ⟨3680224195191662987701103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813931187177767967202941 3680224195191662987701103)
                      ·
                        rfl

theorem cell23_7167211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 1, 1, 3].length) (baseStart_7167211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167211 prefixEnd_7167211 := by exact prefixLift 7167211
  have htrace : WordTrace (prefixWord ++ tailWord_7167211) baseStart_7167211 baseEnd_7167211 := by
    simpa [prefixWord, tailWord_7167211, baseEnd_7167211] using wordTrace_append hprefix tailTrace_7167211
  have hstable : (prefixWord ++ tailWord_7167211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167211).length < 2 ^ (prefixWord ++ tailWord_7167211).sum := by decide
  have hdescent : baseEnd_7167211 < baseStart_7167211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167228 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_7167228 : Nat := 118140960795 + 7167228 * 2 ^ 59
def prefixEnd_7167228 : Nat := 4983230072969 + 3 ^ 40 * 7167228 * 2
def baseEnd_7167228 : Nat := 3680232924362789421188525

theorem tailTrace_7167228 : CollatzResearch.WordTrace tailWord_7167228 prefixEnd_7167228 3680232924362789421188525 := by
  unfold tailWord_7167228
  simp only [CollatzResearch.WordTrace]
  refine ⟨130705140439182247967355169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174273520585576330623140225 130705140439182247967355169)
  ·
    refine ⟨98028855329386685975516377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130705140439182247967355169 98028855329386685975516377)
    ·
      refine ⟨73521641497040014481637283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98028855329386685975516377 73521641497040014481637283)
      ·
        refine ⟨110282462245560021722455925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73521641497040014481637283 110282462245560021722455925)
        ·
          refine ⟨10338980835521252036480243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110282462245560021722455925 10338980835521252036480243)
          ·
            refine ⟨15508471253281878054720365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338980835521252036480243 15508471253281878054720365)
            ·
              refine ⟨5815676719980704270520137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15508471253281878054720365 5815676719980704270520137)
              ·
                refine ⟨4361757539985528202890103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815676719980704270520137 4361757539985528202890103)
                ·
                  refine ⟨6542636309978292304335155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361757539985528202890103 6542636309978292304335155)
                  ·
                    refine ⟨9813954464967438456502733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542636309978292304335155 9813954464967438456502733)
                    ·
                      refine ⟨3680232924362789421188525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9813954464967438456502733 3680232924362789421188525)
                      ·
                        rfl

theorem cell23_7167228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_7167228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167228 prefixEnd_7167228 := by exact prefixLift 7167228
  have htrace : WordTrace (prefixWord ++ tailWord_7167228) baseStart_7167228 baseEnd_7167228 := by
    simpa [prefixWord, tailWord_7167228, baseEnd_7167228] using wordTrace_append hprefix tailTrace_7167228
  have hstable : (prefixWord ++ tailWord_7167228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167228).length < 2 ^ (prefixWord ++ tailWord_7167228).sum := by decide
  have hdescent : baseEnd_7167228 < baseStart_7167228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167244 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_7167244 : Nat := 118140960795 + 7167244 * 2 ^ 59
def prefixEnd_7167244 : Nat := 4983230072969 + 3 ^ 40 * 7167244 * 2
def baseEnd_7167244 : Nat := 1226747046684420452862817

theorem tailTrace_7167244 : CollatzResearch.WordTrace tailWord_7167244 prefixEnd_7167244 1226747046684420452862817 := by
  unfold tailWord_7167244
  simp only [CollatzResearch.WordTrace]
  refine ⟨130705432223153265333646393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174273909630871020444861857 130705432223153265333646393)
  ·
    refine ⟨98029074167364949000234795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130705432223153265333646393 98029074167364949000234795)
    ·
      refine ⟨147043611251047423500352193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98029074167364949000234795 147043611251047423500352193)
      ·
        refine ⟨110282708438285567625264145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147043611251047423500352193 110282708438285567625264145)
        ·
          refine ⟨82712031328714175718948109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110282708438285567625264145 82712031328714175718948109)
          ·
            refine ⟨31017011748267815894605541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82712031328714175718948109 31017011748267815894605541)
            ·
              refine ⟨5815689702800215480238539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31017011748267815894605541 5815689702800215480238539)
              ·
                refine ⟨8723534554200323220357809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815689702800215480238539 8723534554200323220357809)
                ·
                  refine ⟨6542650915650242415268357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723534554200323220357809 6542650915650242415268357)
                  ·
                    refine ⟨1226747046684420452862817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542650915650242415268357 1226747046684420452862817)
                    ·
                      rfl

theorem cell23_7167244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_7167244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167244 prefixEnd_7167244 := by exact prefixLift 7167244
  have htrace : WordTrace (prefixWord ++ tailWord_7167244) baseStart_7167244 baseEnd_7167244 := by
    simpa [prefixWord, tailWord_7167244, baseEnd_7167244] using wordTrace_append hprefix tailTrace_7167244
  have hstable : (prefixWord ++ tailWord_7167244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167244).length < 2 ^ (prefixWord ++ tailWord_7167244).sum := by decide
  have hdescent : baseEnd_7167244 < baseStart_7167244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167267 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3]
def baseStart_7167267 : Nat := 118140960795 + 7167267 * 2 ^ 59
def prefixEnd_7167267 : Nat := 4983230072969 + 3 ^ 40 * 7167267 * 2
def baseEnd_7167267 : Nat := 3680252950108314768600845

theorem tailTrace_7167267 : CollatzResearch.WordTrace tailWord_7167267 prefixEnd_7167267 3680252950108314768600845 := by
  unfold tailWord_7167267
  simp only [CollatzResearch.WordTrace]
  refine ⟨261411703325223205595380055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174274468883482137063586703 261411703325223205595380055)
  ·
    refine ⟨392117554987834808393070083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261411703325223205595380055 392117554987834808393070083)
    ·
      refine ⟨588176332481752212589605125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392117554987834808393070083 588176332481752212589605125)
      ·
        refine ⟨110283062340328539860550961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588176332481752212589605125 110283062340328539860550961)
        ·
          refine ⟨82712296755246404895413221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110283062340328539860550961 82712296755246404895413221)
          ·
            refine ⟨15508555641608700917889979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82712296755246404895413221 15508555641608700917889979)
            ·
              refine ⟨23262833462413051376834969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15508555641608700917889979 23262833462413051376834969)
              ·
                refine ⟨17447125096809788532626227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23262833462413051376834969 17447125096809788532626227)
                ·
                  refine ⟨26170687645214682798939341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17447125096809788532626227 26170687645214682798939341)
                  ·
                    refine ⟨9814007866955506049602253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26170687645214682798939341 9814007866955506049602253)
                    ·
                      refine ⟨3680252950108314768600845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814007866955506049602253 3680252950108314768600845)
                      ·
                        rfl

theorem cell23_7167267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_7167267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167267 prefixEnd_7167267 := by exact prefixLift 7167267
  have htrace : WordTrace (prefixWord ++ tailWord_7167267) baseStart_7167267 baseEnd_7167267 := by
    simpa [prefixWord, tailWord_7167267, baseEnd_7167267] using wordTrace_append hprefix tailTrace_7167267
  have hstable : (prefixWord ++ tailWord_7167267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167267).length < 2 ^ (prefixWord ++ tailWord_7167267).sum := by decide
  have hdescent : baseEnd_7167267 < baseStart_7167267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167285 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_7167285 : Nat := 118140960795 + 7167285 * 2 ^ 59
def prefixEnd_7167285 : Nat := 4983230072969 + 3 ^ 40 * 7167285 * 2
def baseEnd_7167285 : Nat := 3680262192760095698175763

theorem tailTrace_7167285 : CollatzResearch.WordTrace tailWord_7167285 prefixEnd_7167285 3680262192760095698175763 := by
  unfold tailWord_7167285
  simp only [CollatzResearch.WordTrace]
  refine ⟨261412359839157994669535309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174274906559438663113023539 261412359839157994669535309)
  ·
    refine ⟨98029634939684248001075741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261412359839157994669535309 98029634939684248001075741)
    ·
      refine ⟨36761113102381593000403403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98029634939684248001075741 36761113102381593000403403)
      ·
        refine ⟨55141669653572389500605105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36761113102381593000403403 55141669653572389500605105)
        ·
          refine ⟨41356252240179292125453829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55141669653572389500605105 41356252240179292125453829)
          ·
            refine ⟨7754297295033617273522593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41356252240179292125453829 7754297295033617273522593)
            ·
              refine ⟨5815722971275212955141945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754297295033617273522593 5815722971275212955141945)
              ·
                refine ⟨4361792228456409716356459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815722971275212955141945 4361792228456409716356459)
                ·
                  refine ⟨6542688342684614574534689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361792228456409716356459 6542688342684614574534689)
                  ·
                    refine ⟨4907016257013460930901017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542688342684614574534689 4907016257013460930901017)
                    ·
                      refine ⟨3680262192760095698175763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907016257013460930901017 3680262192760095698175763)
                      ·
                        rfl

theorem cell23_7167285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_7167285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167285 prefixEnd_7167285 := by exact prefixLift 7167285
  have htrace : WordTrace (prefixWord ++ tailWord_7167285) baseStart_7167285 baseEnd_7167285 := by
    simpa [prefixWord, tailWord_7167285, baseEnd_7167285] using wordTrace_append hprefix tailTrace_7167285
  have hstable : (prefixWord ++ tailWord_7167285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167285).length < 2 ^ (prefixWord ++ tailWord_7167285).sum := by decide
  have hdescent : baseEnd_7167285 < baseStart_7167285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167290 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_7167290 : Nat := 118140960795 + 7167290 * 2 ^ 59
def prefixEnd_7167290 : Nat := 4983230072969 + 3 ^ 40 * 7167290 * 2
def baseEnd_7167290 : Nat := 3680264760163368178613239

theorem tailTrace_7167290 : CollatzResearch.WordTrace tailWord_7167290 prefixEnd_7167290 3680264760163368178613239 := by
  unfold tailWord_7167290
  simp only [CollatzResearch.WordTrace]
  refine ⟨65353135551034970130866831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174275028136093253682311549 65353135551034970130866831)
  ·
    refine ⟨98029703326552455196300247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65353135551034970130866831 98029703326552455196300247)
    ·
      refine ⟨147044554989828682794450371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98029703326552455196300247 147044554989828682794450371)
      ·
        refine ⟨220566832484743024191675557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147044554989828682794450371 220566832484743024191675557)
        ·
          refine ⟨41356281090889317035939167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220566832484743024191675557 41356281090889317035939167)
          ·
            refine ⟨62034421636333975553908751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41356281090889317035939167 62034421636333975553908751)
            ·
              refine ⟨93051632454500963330863127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62034421636333975553908751 93051632454500963330863127)
              ·
                refine ⟨139577448681751444996294691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93051632454500963330863127 139577448681751444996294691)
                ·
                  refine ⟨209366173022627167494442037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139577448681751444996294691 209366173022627167494442037)
                  ·
                    refine ⟨19628078720871296952603941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209366173022627167494442037 19628078720871296952603941)
                    ·
                      refine ⟨3680264760163368178613239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19628078720871296952603941 3680264760163368178613239)
                      ·
                        rfl

theorem cell23_7167290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_7167290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167290 prefixEnd_7167290 := by exact prefixLift 7167290
  have htrace : WordTrace (prefixWord ++ tailWord_7167290) baseStart_7167290 baseEnd_7167290 := by
    simpa [prefixWord, tailWord_7167290, baseEnd_7167290] using wordTrace_append hprefix tailTrace_7167290
  have hstable : (prefixWord ++ tailWord_7167290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167290).length < 2 ^ (prefixWord ++ tailWord_7167290).sum := by decide
  have hdescent : baseEnd_7167290 < baseStart_7167290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167294 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7167294 : Nat := 118140960795 + 7167294 * 2 ^ 59
def prefixEnd_7167294 : Nat := 4983230072969 + 3 ^ 40 * 7167294 * 2
def baseEnd_7167294 : Nat := 3680266814085986162963221

theorem tailTrace_7167294 : CollatzResearch.WordTrace tailWord_7167294 prefixEnd_7167294 3680266814085986162963221 := by
  unfold tailWord_7167294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676586012015673650826617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174275125397416926137741957 32676586012015673650826617)
  ·
    refine ⟨24507439509011755238119963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32676586012015673650826617 24507439509011755238119963)
    ·
      refine ⟨36761159263517632857179945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507439509011755238119963 36761159263517632857179945)
      ·
        refine ⟨27570869447638224642884959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36761159263517632857179945 27570869447638224642884959)
        ·
          refine ⟨41356304171457336964327439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27570869447638224642884959 41356304171457336964327439)
          ·
            refine ⟨62034456257186005446491159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41356304171457336964327439 62034456257186005446491159)
            ·
              refine ⟨93051684385779008169736739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62034456257186005446491159 93051684385779008169736739)
              ·
                refine ⟨139577526578668512254605109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93051684385779008169736739 139577526578668512254605109)
                ·
                  refine ⟨13085393116750173023869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139577526578668512254605109 13085393116750173023869229)
                  ·
                    refine ⟨4907022418781314883950961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13085393116750173023869229 4907022418781314883950961)
                    ·
                      refine ⟨3680266814085986162963221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907022418781314883950961 3680266814085986162963221)
                      ·
                        rfl

theorem cell23_7167294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7167294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167294 prefixEnd_7167294 := by exact prefixLift 7167294
  have htrace : WordTrace (prefixWord ++ tailWord_7167294) baseStart_7167294 baseEnd_7167294 := by
    simpa [prefixWord, tailWord_7167294, baseEnd_7167294] using wordTrace_append hprefix tailTrace_7167294
  have hstable : (prefixWord ++ tailWord_7167294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167294).length < 2 ^ (prefixWord ++ tailWord_7167294).sum := by decide
  have hdescent : baseEnd_7167294 < baseStart_7167294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167320 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7167320 : Nat := 118140960795 + 7167320 * 2 ^ 59
def prefixEnd_7167320 : Nat := 4983230072969 + 3 ^ 40 * 7167320 * 2
def baseEnd_7167320 : Nat := 3680280164583003061238101

theorem tailTrace_7167320 : CollatzResearch.WordTrace tailWord_7167320 prefixEnd_7167320 3680280164583003061238101 := by
  unfold tailWord_7167320
  simp only [CollatzResearch.WordTrace]
  refine ⟨130706818197015597823529707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174275757596020797098039609 130706818197015597823529707)
  ·
    refine ⟨196060227295523396735294561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130706818197015597823529707 196060227295523396735294561)
    ·
      refine ⟨147045170471642547551470921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196060227295523396735294561 147045170471642547551470921)
      ·
        refine ⟨110283877853731910663603191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147045170471642547551470921 110283877853731910663603191)
        ·
          refine ⟨165425816780597865995404787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110283877853731910663603191 165425816780597865995404787)
          ·
            refine ⟨248138725170896798993107181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165425816780597865995404787 248138725170896798993107181)
            ·
              refine ⟨93052021939086299622415193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248138725170896798993107181 93052021939086299622415193)
              ·
                refine ⟨69789016454314724716811395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93052021939086299622415193 69789016454314724716811395)
                ·
                  refine ⟨104683524681472087075217093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69789016454314724716811395 104683524681472087075217093)
                  ·
                    refine ⟨19628160877776016326603205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104683524681472087075217093 19628160877776016326603205)
                    ·
                      refine ⟨3680280164583003061238101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19628160877776016326603205 3680280164583003061238101)
                      ·
                        rfl

theorem cell23_7167320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7167320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167320 prefixEnd_7167320 := by exact prefixLift 7167320
  have htrace : WordTrace (prefixWord ++ tailWord_7167320) baseStart_7167320 baseEnd_7167320 := by
    simpa [prefixWord, tailWord_7167320, baseEnd_7167320] using wordTrace_append hprefix tailTrace_7167320
  have hstable : (prefixWord ++ tailWord_7167320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167320).length < 2 ^ (prefixWord ++ tailWord_7167320).sum := by decide
  have hdescent : baseEnd_7167320 < baseStart_7167320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167328 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2]
def baseStart_7167328 : Nat := 118140960795 + 7167328 * 2 ^ 59
def prefixEnd_7167328 : Nat := 4983230072969 + 3 ^ 40 * 7167328 * 2
def baseEnd_7167328 : Nat := 3680284272428239029938065

theorem tailTrace_7167328 : CollatzResearch.WordTrace tailWord_7167328 prefixEnd_7167328 3680284272428239029938065 := by
  unfold tailWord_7167328
  simp only [CollatzResearch.WordTrace]
  refine ⟨130706964089001106506675319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174275952118668142008900425 130706964089001106506675319)
  ·
    refine ⟨196060446133501659760012979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130706964089001106506675319 196060446133501659760012979)
    ·
      refine ⟨294090669200252489640019469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196060446133501659760012979 294090669200252489640019469)
      ·
        refine ⟨110284000950094683615007301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294090669200252489640019469 110284000950094683615007301)
        ·
          refine ⟨20678250178142753177813869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110284000950094683615007301 20678250178142753177813869)
          ·
            refine ⟨7754343816803532441680201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20678250178142753177813869 7754343816803532441680201)
            ·
              refine ⟨5815757862602649331260151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754343816803532441680201 5815757862602649331260151)
              ·
                refine ⟨8723636793903973996890227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815757862602649331260151 8723636793903973996890227)
                ·
                  refine ⟨13085455190855960995335341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8723636793903973996890227 13085455190855960995335341)
                  ·
                    refine ⟨4907045696570985373250753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13085455190855960995335341 4907045696570985373250753)
                    ·
                      refine ⟨3680284272428239029938065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907045696570985373250753 3680284272428239029938065)
                      ·
                        rfl

theorem cell23_7167328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_7167328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167328 prefixEnd_7167328 := by exact prefixLift 7167328
  have htrace : WordTrace (prefixWord ++ tailWord_7167328) baseStart_7167328 baseEnd_7167328 := by
    simpa [prefixWord, tailWord_7167328, baseEnd_7167328] using wordTrace_append hprefix tailTrace_7167328
  have hstable : (prefixWord ++ tailWord_7167328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167328).length < 2 ^ (prefixWord ++ tailWord_7167328).sum := by decide
  have hdescent : baseEnd_7167328 < baseStart_7167328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167341 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7167341 : Nat := 118140960795 + 7167341 * 2 ^ 59
def prefixEnd_7167341 : Nat := 4983230072969 + 3 ^ 40 * 7167341 * 2
def baseEnd_7167341 : Nat := 3680290947676747479075505

theorem tailTrace_7167341 : CollatzResearch.WordTrace tailWord_7167341 prefixEnd_7167341 3680290947676747479075505 := by
  unfold tailWord_7167341
  simp only [CollatzResearch.WordTrace]
  refine ⟨261414402326955116233573877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174276268217970077489049251 261414402326955116233573877)
  ·
    refine ⟨24507600218152042146897551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261414402326955116233573877 24507600218152042146897551)
    ·
      refine ⟨36761400327228063220346327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507600218152042146897551 36761400327228063220346327)
      ·
        refine ⟨55142100490842094830519491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36761400327228063220346327 55142100490842094830519491)
        ·
          refine ⟨82713150736263142245779237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55142100490842094830519491 82713150736263142245779237)
          ·
            refine ⟨15508715763049339171083607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82713150736263142245779237 15508715763049339171083607)
            ·
              refine ⟨23263073644574008756625411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15508715763049339171083607 23263073644574008756625411)
              ·
                refine ⟨34894610466861013134938117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23263073644574008756625411 34894610466861013134938117)
                ·
                  refine ⟨6542739462536439962800897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34894610466861013134938117 6542739462536439962800897)
                  ·
                    refine ⟨4907054596902329972100673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542739462536439962800897 4907054596902329972100673)
                    ·
                      refine ⟨3680290947676747479075505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907054596902329972100673 3680290947676747479075505)
                      ·
                        rfl

theorem cell23_7167341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7167341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167341 prefixEnd_7167341 := by exact prefixLift 7167341
  have htrace : WordTrace (prefixWord ++ tailWord_7167341) baseStart_7167341 baseEnd_7167341 := by
    simpa [prefixWord, tailWord_7167341, baseEnd_7167341] using wordTrace_append hprefix tailTrace_7167341
  have hstable : (prefixWord ++ tailWord_7167341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167341).length < 2 ^ (prefixWord ++ tailWord_7167341).sum := by decide
  have hdescent : baseEnd_7167341 < baseStart_7167341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167357 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_7167357 : Nat := 118140960795 + 7167357 * 2 ^ 59
def prefixEnd_7167357 : Nat := 4983230072969 + 3 ^ 40 * 7167357 * 2
def baseEnd_7167357 : Nat := 3680299163367219416475431

theorem tailTrace_7167357 : CollatzResearch.WordTrace tailWord_7167357 prefixEnd_7167357 3680299163367219416475431 := by
  unfold tailWord_7167357
  simp only [CollatzResearch.WordTrace]
  refine ⟨261414985894897150966156325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174276657263264767310770883 261414985894897150966156325)
  ·
    refine ⟨49015309855293215806154311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261414985894897150966156325 49015309855293215806154311)
    ·
      refine ⟨73522964782939823709231467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49015309855293215806154311 73522964782939823709231467)
      ·
        refine ⟨110284447174409735563847201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73522964782939823709231467 110284447174409735563847201)
        ·
          refine ⟨82713335380807301672885401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110284447174409735563847201 82713335380807301672885401)
          ·
            refine ⟨62035001535605476254664051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82713335380807301672885401 62035001535605476254664051)
            ·
              refine ⟨93052502303408214381996077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62035001535605476254664051 93052502303408214381996077)
              ·
                refine ⟨34894688363778080393248529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93052502303408214381996077 34894688363778080393248529)
                ·
                  refine ⟨26171016272833560294936397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34894688363778080393248529 26171016272833560294936397)
                  ·
                    refine ⟨9814131102312585110601149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26171016272833560294936397 9814131102312585110601149)
                    ·
                      refine ⟨3680299163367219416475431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814131102312585110601149 3680299163367219416475431)
                      ·
                        rfl

theorem cell23_7167357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_7167357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167357 prefixEnd_7167357 := by exact prefixLift 7167357
  have htrace : WordTrace (prefixWord ++ tailWord_7167357) baseStart_7167357 baseEnd_7167357 := by
    simpa [prefixWord, tailWord_7167357, baseEnd_7167357] using wordTrace_append hprefix tailTrace_7167357
  have hstable : (prefixWord ++ tailWord_7167357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167357).length < 2 ^ (prefixWord ++ tailWord_7167357).sum := by decide
  have hdescent : baseEnd_7167357 < baseStart_7167357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167394 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7167394 : Nat := 118140960795 + 7167394 * 2 ^ 59
def prefixEnd_7167394 : Nat := 4983230072969 + 3 ^ 40 * 7167394 * 2
def baseEnd_7167394 : Nat := 1226772720717145257237587

theorem tailTrace_7167394 : CollatzResearch.WordTrace tailWord_7167394 prefixEnd_7167394 1226772720717145257237587 := by
  unfold tailWord_7167394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65354083848940776571313309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174277556930508737523502157 65354083848940776571313309)
  ·
    refine ⟨24507781443352791214242491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65354083848940776571313309 24507781443352791214242491)
    ·
      refine ⟨36761672165029186821363737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507781443352791214242491 36761672165029186821363737)
      ·
        refine ⟨27571254123771890116022803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36761672165029186821363737 27571254123771890116022803)
        ·
          refine ⟨41356881185657835174034205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27571254123771890116022803 41356881185657835174034205)
          ·
            refine ⟨15508830444621688190262827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41356881185657835174034205 15508830444621688190262827)
            ·
              refine ⟨23263245666932532285394241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15508830444621688190262827 23263245666932532285394241)
              ·
                refine ⟨17447434250199399214045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23263245666932532285394241 17447434250199399214045681)
                ·
                  refine ⟨13085575687649549410534261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17447434250199399214045681 13085575687649549410534261)
                  ·
                    refine ⟨1226772720717145257237587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13085575687649549410534261 1226772720717145257237587)
                    ·
                      rfl

theorem cell23_7167394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7167394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167394 prefixEnd_7167394 := by exact prefixLift 7167394
  have htrace : WordTrace (prefixWord ++ tailWord_7167394) baseStart_7167394 baseEnd_7167394 := by
    simpa [prefixWord, tailWord_7167394, baseEnd_7167394] using wordTrace_append hprefix tailTrace_7167394
  have hstable : (prefixWord ++ tailWord_7167394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167394).length < 2 ^ (prefixWord ++ tailWord_7167394).sum := by decide
  have hdescent : baseEnd_7167394 < baseStart_7167394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167434 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_7167434 : Nat := 118140960795 + 7167434 * 2 ^ 59
def prefixEnd_7167434 : Nat := 4983230072969 + 3 ^ 40 * 7167434 * 2
def baseEnd_7167434 : Nat := 3680338701377615615212577

theorem tailTrace_7167434 : CollatzResearch.WordTrace tailWord_7167434 prefixEnd_7167434 3680338701377615615212577 := by
  unfold tailWord_7167434
  simp only [CollatzResearch.WordTrace]
  refine ⟨65354448578904548279177339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174278529543745462077806237 65354448578904548279177339)
  ·
    refine ⟨98031672868356822418766009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65354448578904548279177339 98031672868356822418766009)
    ·
      refine ⟨73523754651267616814074507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98031672868356822418766009 73523754651267616814074507)
      ·
        refine ⟨110285631976901425221111761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73523754651267616814074507 110285631976901425221111761)
        ·
          refine ⟨82714223982676068915833821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110285631976901425221111761 82714223982676068915833821)
          ·
            refine ⟨31017833993503525843437683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82714223982676068915833821 31017833993503525843437683)
            ·
              refine ⟨46526750990255288765156525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31017833993503525843437683 46526750990255288765156525)
              ·
                refine ⟨17447531621345733286933697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46526750990255288765156525 17447531621345733286933697)
                ·
                  refine ⟨13085648716009299965200273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17447531621345733286933697 13085648716009299965200273)
                  ·
                    refine ⟨9814236537006974973900205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13085648716009299965200273 9814236537006974973900205)
                    ·
                      refine ⟨3680338701377615615212577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814236537006974973900205 3680338701377615615212577)
                      ·
                        rfl

theorem cell23_7167434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_7167434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167434 prefixEnd_7167434 := by exact prefixLift 7167434
  have htrace : WordTrace (prefixWord ++ tailWord_7167434) baseStart_7167434 baseEnd_7167434 := by
    simpa [prefixWord, tailWord_7167434, baseEnd_7167434] using wordTrace_append hprefix tailTrace_7167434
  have hstable : (prefixWord ++ tailWord_7167434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167434).length < 2 ^ (prefixWord ++ tailWord_7167434).sum := by decide
  have hdescent : baseEnd_7167434 < baseStart_7167434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167497 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_7167497 : Nat := 118140960795 + 7167497 * 2 ^ 59
def prefixEnd_7167497 : Nat := 4983230072969 + 3 ^ 40 * 7167497 * 2
def baseEnd_7167497 : Nat := 1226790350219616289574929

theorem tailTrace_7167497 : CollatzResearch.WordTrace tailWord_7167497 prefixEnd_7167497 1226790350219616289574929 := by
  unfold tailWord_7167497
  simp only [CollatzResearch.WordTrace]
  refine ⟨261420092114389954876252745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174280061409593303250835163 261420092114389954876252745)
  ·
    refine ⟨196065069085792466157189559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261420092114389954876252745 196065069085792466157189559)
    ·
      refine ⟨294097603628688699235784339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196065069085792466157189559 294097603628688699235784339)
      ·
        refine ⟨441146405443033048853676509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294097603628688699235784339 441146405443033048853676509)
        ·
          refine ⟨165429902041137393320128691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441146405443033048853676509 165429902041137393320128691)
          ·
            refine ⟨248144853061706089980193037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165429902041137393320128691 248144853061706089980193037)
            ·
              refine ⟨93054319898139783742572389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248144853061706089980193037 93054319898139783742572389)
              ·
                refine ⟨17447684980901209451732323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93054319898139783742572389 17447684980901209451732323)
                ·
                  refine ⟨26171527471351814177598485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17447684980901209451732323 26171527471351814177598485)
                  ·
                    refine ⟨1226790350219616289574929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26171527471351814177598485 1226790350219616289574929)
                    ·
                      rfl

theorem cell23_7167497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_7167497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167497 prefixEnd_7167497 := by exact prefixLift 7167497
  have htrace : WordTrace (prefixWord ++ tailWord_7167497) baseStart_7167497 baseEnd_7167497 := by
    simpa [prefixWord, tailWord_7167497, baseEnd_7167497] using wordTrace_append hprefix tailTrace_7167497
  have hstable : (prefixWord ++ tailWord_7167497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167497).length < 2 ^ (prefixWord ++ tailWord_7167497).sum := by decide
  have hdescent : baseEnd_7167497 < baseStart_7167497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167498 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_7167498 : Nat := 118140960795 + 7167498 * 2 ^ 59
def prefixEnd_7167498 : Nat := 4983230072969 + 3 ^ 40 * 7167498 * 2
def baseEnd_7167498 : Nat := 3680371564139503364812283

theorem tailTrace_7167498 : CollatzResearch.WordTrace tailWord_7167498 prefixEnd_7167498 3680371564139503364812283 := by
  unfold tailWord_7167498
  simp only [CollatzResearch.WordTrace]
  refine ⟨65355032146846583011759787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174280085724924221364692765 65355032146846583011759787)
  ·
    refine ⟨98032548220269874517639681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65355032146846583011759787 98032548220269874517639681)
    ·
      refine ⟨73524411165202405888229761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98032548220269874517639681 73524411165202405888229761)
      ·
        refine ⟨55143308373901804416172321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73524411165202405888229761 55143308373901804416172321)
        ·
          refine ⟨41357481280426353312129241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55143308373901804416172321 41357481280426353312129241)
          ·
            refine ⟨31018110960319764984096931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41357481280426353312129241 31018110960319764984096931)
            ·
              refine ⟨46527166440479647476145397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31018110960319764984096931 46527166440479647476145397)
              ·
                refine ⟨4361921853794966950888631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46527166440479647476145397 4361921853794966950888631)
                ·
                  refine ⟨6542882780692450426332947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361921853794966950888631 6542882780692450426332947)
                  ·
                    refine ⟨9814324171038675639499421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542882780692450426332947 9814324171038675639499421)
                    ·
                      refine ⟨3680371564139503364812283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814324171038675639499421 3680371564139503364812283)
                      ·
                        rfl

theorem cell23_7167498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_7167498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167498 prefixEnd_7167498 := by exact prefixLift 7167498
  have htrace : WordTrace (prefixWord ++ tailWord_7167498) baseStart_7167498 baseEnd_7167498 := by
    simpa [prefixWord, tailWord_7167498, baseEnd_7167498] using wordTrace_append hprefix tailTrace_7167498
  have hstable : (prefixWord ++ tailWord_7167498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167498).length < 2 ^ (prefixWord ++ tailWord_7167498).sum := by decide
  have hdescent : baseEnd_7167498 < baseStart_7167498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167541 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_7167541 : Nat := 118140960795 + 7167541 * 2 ^ 59
def prefixEnd_7167541 : Nat := 4983230072969 + 3 ^ 40 * 7167541 * 2
def baseEnd_7167541 : Nat := 3680393643807646696574585

theorem tailTrace_7167541 : CollatzResearch.WordTrace tailWord_7167541 prefixEnd_7167541 3680393643807646696574585 := by
  unfold tailWord_7167541
  simp only [CollatzResearch.WordTrace]
  refine ⟨261421696926230550390854477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174281131284153700260569651 261421696926230550390854477)
  ·
    refine ⟨98033136347336456396570429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261421696926230550390854477 98033136347336456396570429)
    ·
      refine ⟨36762426130251171148713911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98033136347336456396570429 36762426130251171148713911)
      ·
        refine ⟨55143639195376756723070867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36762426130251171148713911 55143639195376756723070867)
        ·
          refine ⟨82715458793065135084606301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55143639195376756723070867 82715458793065135084606301)
          ·
            refine ⟨31018297047399425656727363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82715458793065135084606301 31018297047399425656727363)
            ·
              refine ⟨46527445571099138485091045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31018297047399425656727363 46527445571099138485091045)
              ·
                refine ⟨8723896044581088465954571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46527445571099138485091045 8723896044581088465954571)
                ·
                  refine ⟨13085844066871632698931857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8723896044581088465954571 13085844066871632698931857)
                  ·
                    refine ⟨9814383050153724524198893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13085844066871632698931857 9814383050153724524198893)
                    ·
                      refine ⟨3680393643807646696574585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814383050153724524198893 3680393643807646696574585)
                      ·
                        rfl

theorem cell23_7167541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_7167541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167541 prefixEnd_7167541 := by exact prefixLift 7167541
  have htrace : WordTrace (prefixWord ++ tailWord_7167541) baseStart_7167541 baseEnd_7167541 := by
    simpa [prefixWord, tailWord_7167541, baseEnd_7167541] using wordTrace_append hprefix tailTrace_7167541
  have hstable : (prefixWord ++ tailWord_7167541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167541).length < 2 ^ (prefixWord ++ tailWord_7167541).sum := by decide
  have hdescent : baseEnd_7167541 < baseStart_7167541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167544 : List Nat := [2, 1, 2, 1, 4, 2, 4, 7]
def baseStart_7167544 : Nat := 118140960795 + 7167544 * 2 ^ 59
def prefixEnd_7167544 : Nat := 4983230072969 + 3 ^ 40 * 7167544 * 2
def baseEnd_7167544 : Nat := 136310932749985562401373

theorem tailTrace_7167544 : CollatzResearch.WordTrace tailWord_7167544 prefixEnd_7167544 136310932749985562401373 := by
  unfold tailWord_7167544
  simp only [CollatzResearch.WordTrace]
  refine ⟨130710903172609840951606843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174281204230146454602142457 130710903172609840951606843)
  ·
    refine ⟨196066354758914761427410265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130710903172609840951606843 196066354758914761427410265)
    ·
      refine ⟨147049766069186071070557699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196066354758914761427410265 147049766069186071070557699)
      ·
        refine ⟨220574649103779106605836549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147049766069186071070557699 220574649103779106605836549)
        ·
          refine ⟨41357746706958582488594353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220574649103779106605836549 41357746706958582488594353)
          ·
            refine ⟨31018310030218936866445765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41357746706958582488594353 31018310030218936866445765)
            ·
              refine ⟨5815933130666050662458581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31018310030218936866445765 5815933130666050662458581)
              ·
                refine ⟨136310932749985562401373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5815933130666050662458581 136310932749985562401373)
                ·
                  rfl

theorem cell23_7167544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 7].length) (baseStart_7167544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167544 prefixEnd_7167544 := by exact prefixLift 7167544
  have htrace : WordTrace (prefixWord ++ tailWord_7167544) baseStart_7167544 baseEnd_7167544 := by
    simpa [prefixWord, tailWord_7167544, baseEnd_7167544] using wordTrace_append hprefix tailTrace_7167544
  have hstable : (prefixWord ++ tailWord_7167544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167544).length < 2 ^ (prefixWord ++ tailWord_7167544).sum := by decide
  have hdescent : baseEnd_7167544 < baseStart_7167544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167567 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_7167567 : Nat := 118140960795 + 7167567 * 2 ^ 59
def prefixEnd_7167567 : Nat := 4983230072969 + 3 ^ 40 * 7167567 * 2
def baseEnd_7167567 : Nat := 3680406994304663594849465

theorem tailTrace_7167567 : CollatzResearch.WordTrace tailWord_7167567 prefixEnd_7167567 3680406994304663594849465 := by
  unfold tailWord_7167567
  simp only [CollatzResearch.WordTrace]
  refine ⟨261422645224136356831300955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174281763482757571220867303 261422645224136356831300955)
  ·
    refine ⟨392133967836204535246951433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261422645224136356831300955 392133967836204535246951433)
    ·
      refine ⟨294100475877153401435213575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392133967836204535246951433 294100475877153401435213575)
      ·
        refine ⟨441150713815730102152820363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294100475877153401435213575 441150713815730102152820363)
        ·
          refine ⟨661726070723595153229230545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441150713815730102152820363 661726070723595153229230545)
          ·
            refine ⟨496294553042696364921922909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661726070723595153229230545 496294553042696364921922909)
            ·
              refine ⟨186110457391011136845721091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496294553042696364921922909 186110457391011136845721091)
              ·
                refine ⟨279165686086516705268581637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186110457391011136845721091 279165686086516705268581637)
                ·
                  refine ⟨52343566141221882237859057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279165686086516705268581637 52343566141221882237859057)
                  ·
                    refine ⟨39257674605916411678394293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52343566141221882237859057 39257674605916411678394293)
                    ·
                      refine ⟨3680406994304663594849465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39257674605916411678394293 3680406994304663594849465)
                      ·
                        rfl

theorem cell23_7167567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_7167567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167567 prefixEnd_7167567 := by exact prefixLift 7167567
  have htrace : WordTrace (prefixWord ++ tailWord_7167567) baseStart_7167567 baseEnd_7167567 := by
    simpa [prefixWord, tailWord_7167567, baseEnd_7167567] using wordTrace_append hprefix tailTrace_7167567
  have hstable : (prefixWord ++ tailWord_7167567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167567).length < 2 ^ (prefixWord ++ tailWord_7167567).sum := by decide
  have hdescent : baseEnd_7167567 < baseStart_7167567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167572 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_7167572 : Nat := 118140960795 + 7167572 * 2 ^ 59
def prefixEnd_7167572 : Nat := 4983230072969 + 3 ^ 40 * 7167572 * 2
def baseEnd_7167572 : Nat := 3680409561707936075286943

theorem tailTrace_7167572 : CollatzResearch.WordTrace tailWord_7167572 prefixEnd_7167572 3680409561707936075286943 := by
  unfold tailWord_7167572
  simp only [CollatzResearch.WordTrace]
  refine ⟨130711413794559121342616485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174281885059412161790155313 130711413794559121342616485)
  ·
    refine ⟨24508390086479835251740591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130711413794559121342616485 24508390086479835251740591)
    ·
      refine ⟨36762585129719752877610887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24508390086479835251740591 36762585129719752877610887)
      ·
        refine ⟨55143877694579629316416331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36762585129719752877610887 55143877694579629316416331)
        ·
          refine ⟨82715816541869443974624497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55143877694579629316416331 82715816541869443974624497)
          ·
            refine ⟨62036862406402082980968373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82715816541869443974624497 62036862406402082980968373)
            ·
              refine ⟨5815955850600195279465785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62036862406402082980968373 5815955850600195279465785)
              ·
                refine ⟨4361966887950146459599339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815955850600195279465785 4361966887950146459599339)
                ·
                  refine ⟨6542950331925219689399009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361966887950146459599339 6542950331925219689399009)
                  ·
                    refine ⟨4907212748943914767049257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542950331925219689399009 4907212748943914767049257)
                    ·
                      refine ⟨3680409561707936075286943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907212748943914767049257 3680409561707936075286943)
                      ·
                        rfl

theorem cell23_7167572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_7167572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167572 prefixEnd_7167572 := by exact prefixLift 7167572
  have htrace : WordTrace (prefixWord ++ tailWord_7167572) baseStart_7167572 baseEnd_7167572 := by
    simpa [prefixWord, tailWord_7167572, baseEnd_7167572] using wordTrace_append hprefix tailTrace_7167572
  have hstable : (prefixWord ++ tailWord_7167572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167572).length < 2 ^ (prefixWord ++ tailWord_7167572).sum := by decide
  have hdescent : baseEnd_7167572 < baseStart_7167572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167588 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_7167588 : Nat := 118140960795 + 7167588 * 2 ^ 59
def prefixEnd_7167588 : Nat := 4983230072969 + 3 ^ 40 * 7167588 * 2
def baseEnd_7167588 : Nat := 3680417777398408012686869

theorem tailTrace_7167588 : CollatzResearch.WordTrace tailWord_7167588 prefixEnd_7167588 3680417777398408012686869 := by
  unfold tailWord_7167588
  simp only [CollatzResearch.WordTrace]
  refine ⟨130711705578530138708907709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174282274104706851611876945 130711705578530138708907709)
  ·
    refine ⟨49016889591948802015840391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130711705578530138708907709 49016889591948802015840391)
    ·
      refine ⟨73525334387923203023760587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49016889591948802015840391 73525334387923203023760587)
      ·
        refine ⟨110288001581884804535640881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73525334387923203023760587 110288001581884804535640881)
        ·
          refine ⟨82716001186413603401730661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110288001581884804535640881 82716001186413603401730661)
          ·
            refine ⟨15509250222452550637824499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82716001186413603401730661 15509250222452550637824499)
            ·
              refine ⟨23263875333678825956736749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15509250222452550637824499 23263875333678825956736749)
              ·
                refine ⟨8723953250129559733776281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23263875333678825956736749 8723953250129559733776281)
                ·
                  refine ⟨6542964937597169800332211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723953250129559733776281 6542964937597169800332211)
                  ·
                    refine ⟨9814447406395754700498317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542964937597169800332211 9814447406395754700498317)
                    ·
                      refine ⟨3680417777398408012686869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814447406395754700498317 3680417777398408012686869)
                      ·
                        rfl

theorem cell23_7167588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_7167588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167588 prefixEnd_7167588 := by exact prefixLift 7167588
  have htrace : WordTrace (prefixWord ++ tailWord_7167588) baseStart_7167588 baseEnd_7167588 := by
    simpa [prefixWord, tailWord_7167588, baseEnd_7167588] using wordTrace_append hprefix tailTrace_7167588
  have hstable : (prefixWord ++ tailWord_7167588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167588).length < 2 ^ (prefixWord ++ tailWord_7167588).sum := by decide
  have hdescent : baseEnd_7167588 < baseStart_7167588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167611 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 4, 2]
def baseStart_7167611 : Nat := 118140960795 + 7167611 * 2 ^ 59
def prefixEnd_7167611 : Nat := 4983230072969 + 3 ^ 40 * 7167611 * 2
def baseEnd_7167611 : Nat := 3680429587453461422699263

theorem tailTrace_7167611 : CollatzResearch.WordTrace tailWord_7167611 prefixEnd_7167611 3680429587453461422699263 := by
  unfold tailWord_7167611
  simp only [CollatzResearch.WordTrace]
  refine ⟨261424250035976952345902687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174282833357317968230601791 261424250035976952345902687)
  ·
    refine ⟨392136375053965428518854031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261424250035976952345902687 392136375053965428518854031)
    ·
      refine ⟨588204562580948142778281047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392136375053965428518854031 588204562580948142778281047)
      ·
        refine ⟨882306843871422214167421571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588204562580948142778281047 882306843871422214167421571)
        ·
          refine ⟨1323460265807133321251132357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882306843871422214167421571 1323460265807133321251132357)
          ·
            refine ⟨248148799838837497734587317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1323460265807133321251132357 248148799838837497734587317)
            ·
              refine ⟨23263949984891015412617561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248148799838837497734587317 23263949984891015412617561)
              ·
                refine ⟨17447962488668261559463171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23263949984891015412617561 17447962488668261559463171)
                ·
                  refine ⟨26171943733002392339194757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17447962488668261559463171 26171943733002392339194757)
                  ·
                    refine ⟨4907239449937948563599017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26171943733002392339194757 4907239449937948563599017)
                    ·
                      refine ⟨3680429587453461422699263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907239449937948563599017 3680429587453461422699263)
                      ·
                        rfl

theorem cell23_7167611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4, 2].length) (baseStart_7167611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167611 prefixEnd_7167611 := by exact prefixLift 7167611
  have htrace : WordTrace (prefixWord ++ tailWord_7167611) baseStart_7167611 baseEnd_7167611 := by
    simpa [prefixWord, tailWord_7167611, baseEnd_7167611] using wordTrace_append hprefix tailTrace_7167611
  have hstable : (prefixWord ++ tailWord_7167611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167611).length < 2 ^ (prefixWord ++ tailWord_7167611).sum := by decide
  have hdescent : baseEnd_7167611 < baseStart_7167611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167661 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7167661 : Nat := 118140960795 + 7167661 * 2 ^ 59
def prefixEnd_7167661 : Nat := 4983230072969 + 3 ^ 40 * 7167661 * 2
def baseEnd_7167661 : Nat := 3680455261486186227074033

theorem tailTrace_7167661 : CollatzResearch.WordTrace tailWord_7167661 prefixEnd_7167661 3680455261486186227074033 := by
  unfold tailWord_7167661
  simp only [CollatzResearch.WordTrace]
  refine ⟨261426073685795810885222837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174284049123863873923481891 261426073685795810885222837)
  ·
    refine ⟨24508694408043357270489641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261426073685795810885222837 24508694408043357270489641)
    ·
      refine ⟨18381520806032517952867231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24508694408043357270489641 18381520806032517952867231)
      ·
        refine ⟨27572281209048776929300847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381520806032517952867231 27572281209048776929300847)
        ·
          refine ⟨41358421813573165393951271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27572281209048776929300847 41358421813573165393951271)
          ·
            refine ⟨62037632720359748090926907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41358421813573165393951271 62037632720359748090926907)
            ·
              refine ⟨93056449080539622136390361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62037632720359748090926907 93056449080539622136390361)
              ·
                refine ⟨69792336810404716602292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93056449080539622136390361 69792336810404716602292771)
                ·
                  refine ⟨104688505215607074903439157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69792336810404716602292771 104688505215607074903439157)
                  ·
                    refine ⟨9814547363963163272197421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104688505215607074903439157 9814547363963163272197421)
                    ·
                      refine ⟨3680455261486186227074033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814547363963163272197421 3680455261486186227074033)
                      ·
                        rfl

theorem cell23_7167661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7167661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167661 prefixEnd_7167661 := by exact prefixLift 7167661
  have htrace : WordTrace (prefixWord ++ tailWord_7167661) baseStart_7167661 baseEnd_7167661 := by
    simpa [prefixWord, tailWord_7167661, baseEnd_7167661] using wordTrace_append hprefix tailTrace_7167661
  have hstable : (prefixWord ++ tailWord_7167661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167661).length < 2 ^ (prefixWord ++ tailWord_7167661).sum := by decide
  have hdescent : baseEnd_7167661 < baseStart_7167661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167711 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 3, 4]
def baseStart_7167711 : Nat := 118140960795 + 7167711 * 2 ^ 59
def prefixEnd_7167711 : Nat := 4983230072969 + 3 ^ 40 * 7167711 * 2
def baseEnd_7167711 : Nat := 1226826978506303677149601

theorem tailTrace_7167711 : CollatzResearch.WordTrace tailWord_7167711 prefixEnd_7167711 1226826978506303677149601 := by
  unfold tailWord_7167711
  simp only [CollatzResearch.WordTrace]
  refine ⟨261427897335614669424542987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174285264890409779616361991 261427897335614669424542987)
  ·
    refine ⟨392141846003422004136814481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261427897335614669424542987 392141846003422004136814481)
    ·
      refine ⟨294106384502566503102610861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392141846003422004136814481 294106384502566503102610861)
      ·
        refine ⟨110289894188462438663479073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294106384502566503102610861 110289894188462438663479073)
        ·
          refine ⟨82717420641346828997609305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110289894188462438663479073 82717420641346828997609305)
          ·
            refine ⟨62038065481010121748206979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82717420641346828997609305 62038065481010121748206979)
            ·
              refine ⟨93057098221515182622310469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62038065481010121748206979 93057098221515182622310469)
              ·
                refine ⟨17448205916534096741683213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93057098221515182622310469 17448205916534096741683213)
                ·
                  refine ⟨6543077218700286278131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17448205916534096741683213 6543077218700286278131205)
                  ·
                    refine ⟨1226826978506303677149601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6543077218700286278131205 1226826978506303677149601)
                    ·
                      rfl

theorem cell23_7167711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_7167711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167711 prefixEnd_7167711 := by exact prefixLift 7167711
  have htrace : WordTrace (prefixWord ++ tailWord_7167711) baseStart_7167711 baseEnd_7167711 := by
    simpa [prefixWord, tailWord_7167711, baseEnd_7167711] using wordTrace_append hprefix tailTrace_7167711
  have hstable : (prefixWord ++ tailWord_7167711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167711).length < 2 ^ (prefixWord ++ tailWord_7167711).sum := by decide
  have hdescent : baseEnd_7167711 < baseStart_7167711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167721 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_7167721 : Nat := 118140960795 + 7167721 * 2 ^ 59
def prefixEnd_7167721 : Nat := 4983230072969 + 3 ^ 40 * 7167721 * 2
def baseEnd_7167721 : Nat := 3680486070325455992323757

theorem tailTrace_7167721 : CollatzResearch.WordTrace tailWord_7167721 prefixEnd_7167721 3680486070325455992323757 := by
  unfold tailWord_7167721
  simp only [CollatzResearch.WordTrace]
  refine ⟨261428262065578441132407017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174285508043718960754938011 261428262065578441132407017)
  ·
    refine ⟨196071196549183830849305263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261428262065578441132407017 196071196549183830849305263)
    ·
      refine ⟨294106794823775746273957895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196071196549183830849305263 294106794823775746273957895)
      ·
        refine ⟨441160192235663619410936843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294106794823775746273957895 441160192235663619410936843)
        ·
          refine ⟨661740288353495429116405265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441160192235663619410936843 661740288353495429116405265)
          ·
            refine ⟨496305216265121571837303949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661740288353495429116405265 496305216265121571837303949)
            ·
              refine ⟨186114456099420589438988981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496305216265121571837303949 186114456099420589438988981)
              ·
                refine ⟨17448230259320680259905217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186114456099420589438988981 17448230259320680259905217)
                ·
                  refine ⟨13086172694490510194928913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17448230259320680259905217 13086172694490510194928913)
                  ·
                    refine ⟨9814629520867882646196685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13086172694490510194928913 9814629520867882646196685)
                    ·
                      refine ⟨3680486070325455992323757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814629520867882646196685 3680486070325455992323757)
                      ·
                        rfl

theorem cell23_7167721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_7167721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167721 prefixEnd_7167721 := by exact prefixLift 7167721
  have htrace : WordTrace (prefixWord ++ tailWord_7167721) baseStart_7167721 baseEnd_7167721 := by
    simpa [prefixWord, tailWord_7167721, baseEnd_7167721] using wordTrace_append hprefix tailTrace_7167721
  have hstable : (prefixWord ++ tailWord_7167721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167721).length < 2 ^ (prefixWord ++ tailWord_7167721).sum := by decide
  have hdescent : baseEnd_7167721 < baseStart_7167721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167724 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 8]
def baseStart_7167724 : Nat := 118140960795 + 7167724 * 2 ^ 59
def prefixEnd_7167724 : Nat := 4983230072969 + 3 ^ 40 * 7167724 * 2
def baseEnd_7167724 : Nat := 408943067863046608954027

theorem tailTrace_7167724 : CollatzResearch.WordTrace tailWord_7167724 prefixEnd_7167724 408943067863046608954027 := by
  unfold tailWord_7167724
  simp only [CollatzResearch.WordTrace]
  refine ⟨130714185742283786322383113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174285580989711715096510817 130714185742283786322383113)
  ·
    refine ⟨98035639306712839741787335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130714185742283786322383113 98035639306712839741787335)
    ·
      refine ⟨147053458960069259612681003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98035639306712839741787335 147053458960069259612681003)
      ·
        refine ⟨220580188440103889419021505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147053458960069259612681003 220580188440103889419021505)
        ·
          refine ⟨165435141330077917064266129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220580188440103889419021505 165435141330077917064266129)
          ·
            refine ⟨124076355997558437798199597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165435141330077917064266129 124076355997558437798199597)
            ·
              refine ⟨46528633499084414174324849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124076355997558437798199597 46528633499084414174324849)
              ·
                refine ⟨34896475124313310630743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46528633499084414174324849 34896475124313310630743637)
                ·
                  refine ⟨408943067863046608954027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34896475124313310630743637 408943067863046608954027)
                  ·
                    rfl

theorem cell23_7167724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_7167724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167724 prefixEnd_7167724 := by exact prefixLift 7167724
  have htrace : WordTrace (prefixWord ++ tailWord_7167724) baseStart_7167724 baseEnd_7167724 := by
    simpa [prefixWord, tailWord_7167724, baseEnd_7167724] using wordTrace_append hprefix tailTrace_7167724
  have hstable : (prefixWord ++ tailWord_7167724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167724).length < 2 ^ (prefixWord ++ tailWord_7167724).sum := by decide
  have hdescent : baseEnd_7167724 < baseStart_7167724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167728 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 1, 4]
def baseStart_7167728 : Nat := 118140960795 + 7167728 * 2 ^ 59
def prefixEnd_7167728 : Nat := 4983230072969 + 3 ^ 40 * 7167728 * 2
def baseEnd_7167728 : Nat := 1226829888230012488312075

theorem tailTrace_7167728 : CollatzResearch.WordTrace tailWord_7167728 prefixEnd_7167728 1226829888230012488312075 := by
  unfold tailWord_7167728
  simp only [CollatzResearch.WordTrace]
  refine ⟨130714258688276540663955919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174285678251035387551941225 130714258688276540663955919)
  ·
    refine ⟨196071388032414810995933879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130714258688276540663955919 196071388032414810995933879)
    ·
      refine ⟨294107082048622216493900819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196071388032414810995933879 294107082048622216493900819)
      ·
        refine ⟨441160623072933324740851229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294107082048622216493900819 441160623072933324740851229)
        ·
          refine ⟨165435233652349996777819211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441160623072933324740851229 165435233652349996777819211)
          ·
            refine ⟨248152850478524995166728817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165435233652349996777819211 248152850478524995166728817)
            ·
              refine ⟨186114637858893746375046613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248152850478524995166728817 186114637858893746375046613)
              ·
                refine ⟨4362061824817822180665155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186114637858893746375046613 4362061824817822180665155)
                ·
                  refine ⟨6543092737226733270997733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362061824817822180665155 6543092737226733270997733)
                  ·
                    refine ⟨1226829888230012488312075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6543092737226733270997733 1226829888230012488312075)
                    ·
                      rfl

theorem cell23_7167728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_7167728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167728 prefixEnd_7167728 := by exact prefixLift 7167728
  have htrace : WordTrace (prefixWord ++ tailWord_7167728) baseStart_7167728 baseEnd_7167728 := by
    simpa [prefixWord, tailWord_7167728, baseEnd_7167728] using wordTrace_append hprefix tailTrace_7167728
  have hstable : (prefixWord ++ tailWord_7167728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167728).length < 2 ^ (prefixWord ++ tailWord_7167728).sum := by decide
  have hdescent : baseEnd_7167728 < baseStart_7167728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167758 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_7167758 : Nat := 118140960795 + 7167758 * 2 ^ 59
def prefixEnd_7167758 : Nat := 4983230072969 + 3 ^ 40 * 7167758 * 2
def baseEnd_7167758 : Nat := 408945007678852483062343

theorem tailTrace_7167758 : CollatzResearch.WordTrace tailWord_7167758 prefixEnd_7167758 408945007678852483062343 := by
  unfold tailWord_7167758
  simp only [CollatzResearch.WordTrace]
  refine ⟨32678701445805549556437991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174286407710962930967669285 32678701445805549556437991)
  ·
    refine ⟨49018052168708324334656987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32678701445805549556437991 49018052168708324334656987)
    ·
      refine ⟨73527078253062486501985481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49018052168708324334656987 73527078253062486501985481)
      ·
        refine ⟨55145308689796864876489111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73527078253062486501985481 55145308689796864876489111)
        ·
          refine ⟨82717963034695297314733667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55145308689796864876489111 82717963034695297314733667)
          ·
            refine ⟨124076944552042945972100501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82717963034695297314733667 124076944552042945972100501)
            ·
              refine ⟨5816106775877013092442211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124076944552042945972100501 5816106775877013092442211)
              ·
                refine ⟨8724160163815519638663317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816106775877013092442211 8724160163815519638663317)
                ·
                  refine ⟨408945007678852483062343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8724160163815519638663317 408945007678852483062343)
                  ·
                    rfl

theorem cell23_7167758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_7167758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167758 prefixEnd_7167758 := by exact prefixLift 7167758
  have htrace : WordTrace (prefixWord ++ tailWord_7167758) baseStart_7167758 baseEnd_7167758 := by
    simpa [prefixWord, tailWord_7167758, baseEnd_7167758] using wordTrace_append hprefix tailTrace_7167758
  have hstable : (prefixWord ++ tailWord_7167758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167758).length < 2 ^ (prefixWord ++ tailWord_7167758).sum := by decide
  have hdescent : baseEnd_7167758 < baseStart_7167758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167768 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7167768 : Nat := 118140960795 + 7167768 * 2 ^ 59
def prefixEnd_7167768 : Nat := 4983230072969 + 3 ^ 40 * 7167768 * 2
def baseEnd_7167768 : Nat := 3680510203916217308436041

theorem tailTrace_7167768 : CollatzResearch.WordTrace tailWord_7167768 prefixEnd_7167768 3680510203916217308436041 := by
  unfold tailWord_7167768
  simp only [CollatzResearch.WordTrace]
  refine ⟨130714988148204084079683979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174286650864272112106245305 130714988148204084079683979)
  ·
    refine ⟨196072482222306126119525969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130714988148204084079683979 196072482222306126119525969)
    ·
      refine ⟨147054361666729594589644477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196072482222306126119525969 147054361666729594589644477)
      ·
        refine ⟨55145385625023597971116679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147054361666729594589644477 55145385625023597971116679)
        ·
          refine ⟨82718078437535396956675019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55145385625023597971116679 82718078437535396956675019)
          ·
            refine ⟨124077117656303095435012529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82718078437535396956675019 124077117656303095435012529)
            ·
              refine ⟨93057838242227321576259397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124077117656303095435012529 93057838242227321576259397)
              ·
                refine ⟨17448344670417622795548637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93057838242227321576259397 17448344670417622795548637)
                ·
                  refine ⟨6543129251406608548330739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17448344670417622795548637 6543129251406608548330739)
                  ·
                    refine ⟨9814693877109912822496109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543129251406608548330739 9814693877109912822496109)
                    ·
                      refine ⟨3680510203916217308436041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814693877109912822496109 3680510203916217308436041)
                      ·
                        rfl

theorem cell23_7167768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7167768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167768 prefixEnd_7167768 := by exact prefixLift 7167768
  have htrace : WordTrace (prefixWord ++ tailWord_7167768) baseStart_7167768 baseEnd_7167768 := by
    simpa [prefixWord, tailWord_7167768, baseEnd_7167768] using wordTrace_append hprefix tailTrace_7167768
  have hstable : (prefixWord ++ tailWord_7167768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167768).length < 2 ^ (prefixWord ++ tailWord_7167768).sum := by decide
  have hdescent : baseEnd_7167768 < baseStart_7167768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167802 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_7167802 : Nat := 118140960795 + 7167802 * 2 ^ 59
def prefixEnd_7167802 : Nat := 4983230072969 + 3 ^ 40 * 7167802 * 2
def baseEnd_7167802 : Nat := 3680527662258470175410885

theorem tailTrace_7167802 : CollatzResearch.WordTrace tailWord_7167802 prefixEnd_7167802 3680527662258470175410885 := by
  unfold tailWord_7167802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65357804094571247991526415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174287477585523327977403773 65357804094571247991526415)
  ·
    refine ⟨98036706141856871987289623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65357804094571247991526415 98036706141856871987289623)
    ·
      refine ⟨147055059212785307980934435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98036706141856871987289623 147055059212785307980934435)
      ·
        refine ⟨220582588819177961971401653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147055059212785307980934435 220582588819177961971401653)
        ·
          refine ⟨20679617701797933934818905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220582588819177961971401653 20679617701797933934818905)
          ·
            refine ⟨15509713276348450451114179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20679617701797933934818905 15509713276348450451114179)
            ·
              refine ⟨23264569914522675676671269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15509713276348450451114179 23264569914522675676671269)
              ·
                refine ⟨4362106858973001689375863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23264569914522675676671269 4362106858973001689375863)
                ·
                  refine ⟨6543160288459502534063795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362106858973001689375863 6543160288459502534063795)
                  ·
                    refine ⟨9814740432689253801095693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543160288459502534063795 9814740432689253801095693)
                    ·
                      refine ⟨3680527662258470175410885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814740432689253801095693 3680527662258470175410885)
                      ·
                        rfl

theorem cell23_7167802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_7167802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167802 prefixEnd_7167802 := by exact prefixLift 7167802
  have htrace : WordTrace (prefixWord ++ tailWord_7167802) baseStart_7167802 baseEnd_7167802 := by
    simpa [prefixWord, tailWord_7167802, baseEnd_7167802] using wordTrace_append hprefix tailTrace_7167802
  have hstable : (prefixWord ++ tailWord_7167802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167802).length < 2 ^ (prefixWord ++ tailWord_7167802).sum := by decide
  have hdescent : baseEnd_7167802 < baseStart_7167802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167818 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_7167818 : Nat := 118140960795 + 7167818 * 2 ^ 59
def prefixEnd_7167818 : Nat := 4983230072969 + 3 ^ 40 * 7167818 * 2
def baseEnd_7167818 : Nat := 1226845292649647370936937

theorem tailTrace_7167818 : CollatzResearch.WordTrace tailWord_7167818 prefixEnd_7167818 1226845292649647370936937 := by
  unfold tailWord_7167818
  simp only [CollatzResearch.WordTrace]
  refine ⟨65357949986556756674672027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174287866630818017799125405 65357949986556756674672027)
  ·
    refine ⟨98036924979835135012008041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65357949986556756674672027 98036924979835135012008041)
    ·
      refine ⟨73527693734876351259006031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98036924979835135012008041 73527693734876351259006031)
      ·
        refine ⟨110291540602314526888509047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73527693734876351259006031 110291540602314526888509047)
        ·
          refine ⟨165437310903471790332763571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110291540602314526888509047 165437310903471790332763571)
          ·
            refine ⟨248155966355207685499145357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165437310903471790332763571 248155966355207685499145357)
            ·
              refine ⟨93058487383202882062179509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248155966355207685499145357 93058487383202882062179509)
              ·
                refine ⟨8724233192175270193329329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93058487383202882062179509 8724233192175270193329329)
                ·
                  refine ⟨6543174894131452644996997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8724233192175270193329329 6543174894131452644996997)
                  ·
                    refine ⟨1226845292649647370936937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6543174894131452644996997 1226845292649647370936937)
                    ·
                      rfl

theorem cell23_7167818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_7167818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167818 prefixEnd_7167818 := by exact prefixLift 7167818
  have htrace : WordTrace (prefixWord ++ tailWord_7167818) baseStart_7167818 baseEnd_7167818 := by
    simpa [prefixWord, tailWord_7167818, baseEnd_7167818] using wordTrace_append hprefix tailTrace_7167818
  have hstable : (prefixWord ++ tailWord_7167818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167818).length < 2 ^ (prefixWord ++ tailWord_7167818).sum := by decide
  have hdescent : baseEnd_7167818 < baseStart_7167818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167825 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_7167825 : Nat := 118140960795 + 7167825 * 2 ^ 59
def prefixEnd_7167825 : Nat := 4983230072969 + 3 ^ 40 * 7167825 * 2
def baseEnd_7167825 : Nat := 3680539472313523585423279

theorem tailTrace_7167825 : CollatzResearch.WordTrace tailWord_7167825 prefixEnd_7167825 3680539472313523585423279 := by
  unfold tailWord_7167825
  simp only [CollatzResearch.WordTrace]
  refine ⟨261432055257201666894192929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174288036838134444596128619 261432055257201666894192929)
  ·
    refine ⟨196074041442901250170644697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261432055257201666894192929 196074041442901250170644697)
    ·
      refine ⟨147055531082175937627983523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196074041442901250170644697 147055531082175937627983523)
      ·
        refine ⟨220583296623263906441975285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147055531082175937627983523 220583296623263906441975285)
        ·
          refine ⟨20679684058430991228935183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220583296623263906441975285 20679684058430991228935183)
          ·
            refine ⟨31019526087646486843402775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20679684058430991228935183 31019526087646486843402775)
            ·
              refine ⟨46529289131469730265104163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31019526087646486843402775 46529289131469730265104163)
              ·
                refine ⟨69793933697204595397656245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46529289131469730265104163 69793933697204595397656245)
                ·
                  refine ⟨6543181284112930818530273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69793933697204595397656245 6543181284112930818530273)
                  ·
                    refine ⟨4907385963084698113897705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543181284112930818530273 4907385963084698113897705)
                    ·
                      refine ⟨3680539472313523585423279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907385963084698113897705 3680539472313523585423279)
                      ·
                        rfl

theorem cell23_7167825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_7167825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167825 prefixEnd_7167825 := by exact prefixLift 7167825
  have htrace : WordTrace (prefixWord ++ tailWord_7167825) baseStart_7167825 baseEnd_7167825 := by
    simpa [prefixWord, tailWord_7167825, baseEnd_7167825] using wordTrace_append hprefix tailTrace_7167825
  have hstable : (prefixWord ++ tailWord_7167825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167825).length < 2 ^ (prefixWord ++ tailWord_7167825).sum := by decide
  have hdescent : baseEnd_7167825 < baseStart_7167825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167842 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7167842 : Nat := 118140960795 + 7167842 * 2 ^ 59
def prefixEnd_7167842 : Nat := 4983230072969 + 3 ^ 40 * 7167842 * 2
def baseEnd_7167842 : Nat := 3680548201484650018910701

theorem tailTrace_7167842 : CollatzResearch.WordTrace tailWord_7167842 prefixEnd_7167842 3680548201484650018910701 := by
  unfold tailWord_7167842
  simp only [CollatzResearch.WordTrace]
  refine ⟨65358168824535019699390445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174288450198760052531707853 65358168824535019699390445)
  ·
    refine ⟨24509313309200632387271417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65358168824535019699390445 24509313309200632387271417)
    ·
      refine ⟨18381984981900474290453563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24509313309200632387271417 18381984981900474290453563)
      ·
        refine ⟨27572977472850711435680345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381984981900474290453563 27572977472850711435680345)
        ·
          refine ⟨20679733104638033576760259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27572977472850711435680345 20679733104638033576760259)
          ·
            refine ⟨31019599656957050365140389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20679733104638033576760259 31019599656957050365140389)
            ·
              refine ⟨5816174935679446943463823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31019599656957050365140389 5816174935679446943463823)
              ·
                refine ⟨8724262403519170415195735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816174935679446943463823 8724262403519170415195735)
                ·
                  refine ⟨13086393605278755622793603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8724262403519170415195735 13086393605278755622793603)
                  ·
                    refine ⟨19629590407918133434190405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13086393605278755622793603 19629590407918133434190405)
                    ·
                      refine ⟨3680548201484650018910701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19629590407918133434190405 3680548201484650018910701)
                      ·
                        rfl

theorem cell23_7167842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7167842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167842 prefixEnd_7167842 := by exact prefixLift 7167842
  have htrace : WordTrace (prefixWord ++ tailWord_7167842) baseStart_7167842 baseEnd_7167842 := by
    simpa [prefixWord, tailWord_7167842, baseEnd_7167842] using wordTrace_append hprefix tailTrace_7167842
  have hstable : (prefixWord ++ tailWord_7167842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167842).length < 2 ^ (prefixWord ++ tailWord_7167842).sum := by decide
  have hdescent : baseEnd_7167842 < baseStart_7167842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167875 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 3]
def baseStart_7167875 : Nat := 118140960795 + 7167875 * 2 ^ 59
def prefixEnd_7167875 : Nat := 4983230072969 + 3 ^ 40 * 7167875 * 2
def baseEnd_7167875 : Nat := 3680565146346248389798049

theorem tailTrace_7167875 : CollatzResearch.WordTrace tailWord_7167875 prefixEnd_7167875 3680565146346248389798049 := by
  unfold tailWord_7167875
  simp only [CollatzResearch.WordTrace]
  refine ⟨261433878907020525433513079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174289252604680350289008719 261433878907020525433513079)
  ·
    refine ⟨392150818360530788150269619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261433878907020525433513079 392150818360530788150269619)
    ·
      refine ⟨588226227540796182225404429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392150818360530788150269619 588226227540796182225404429)
      ·
        refine ⟨220584835327798568334526661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588226227540796182225404429 220584835327798568334526661)
        ·
          refine ⟨41359656623962231562723749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220584835327798568334526661 41359656623962231562723749)
          ·
            refine ⟨7754935616992918418010703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41359656623962231562723749 7754935616992918418010703)
            ·
              refine ⟨11632403425489377627016055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754935616992918418010703 11632403425489377627016055)
              ·
                refine ⟨17448605138234066440524083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11632403425489377627016055 17448605138234066440524083)
                ·
                  refine ⟨26172907707351099660786125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17448605138234066440524083 26172907707351099660786125)
                  ·
                    refine ⟨9814840390256662372794797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26172907707351099660786125 9814840390256662372794797)
                    ·
                      refine ⟨3680565146346248389798049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9814840390256662372794797 3680565146346248389798049)
                      ·
                        rfl

theorem cell23_7167875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_7167875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167875 prefixEnd_7167875 := by exact prefixLift 7167875
  have htrace : WordTrace (prefixWord ++ tailWord_7167875) baseStart_7167875 baseEnd_7167875 := by
    simpa [prefixWord, tailWord_7167875, baseEnd_7167875] using wordTrace_append hprefix tailTrace_7167875
  have hstable : (prefixWord ++ tailWord_7167875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167875).length < 2 ^ (prefixWord ++ tailWord_7167875).sum := by decide
  have hdescent : baseEnd_7167875 < baseStart_7167875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167882 : List Nat := [3, 1, 2, 4, 3, 1, 2, 7]
def baseStart_7167882 : Nat := 118140960795 + 7167882 * 2 ^ 59
def prefixEnd_7167882 : Nat := 4983230072969 + 3 ^ 40 * 7167882 * 2
def baseEnd_7167882 : Nat := 136317360767067772681871

theorem tailTrace_7167882 : CollatzResearch.WordTrace tailWord_7167882 prefixEnd_7167882 136317360767067772681871 := by
  unfold tailWord_7167882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65358533554498791407254475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174289422811996777086011933 65358533554498791407254475)
  ·
    refine ⟨98037800331748187110881713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65358533554498791407254475 98037800331748187110881713)
    ·
      refine ⟨73528350248811140333161285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98037800331748187110881713 73528350248811140333161285)
      ·
        refine ⟨13786565671652088812467741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73528350248811140333161285 13786565671652088812467741)
        ·
          refine ⟨5169962126869533304675403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13786565671652088812467741 5169962126869533304675403)
          ·
            refine ⟨7754943190304299957013105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169962126869533304675403 7754943190304299957013105)
            ·
              refine ⟨5816207392728224967759829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754943190304299957013105 5816207392728224967759829)
              ·
                refine ⟨136317360767067772681871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5816207392728224967759829 136317360767067772681871)
                ·
                  rfl

theorem cell23_7167882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_7167882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167882 prefixEnd_7167882 := by exact prefixLift 7167882
  have htrace : WordTrace (prefixWord ++ tailWord_7167882) baseStart_7167882 baseEnd_7167882 := by
    simpa [prefixWord, tailWord_7167882, baseEnd_7167882] using wordTrace_append hprefix tailTrace_7167882
  have hstable : (prefixWord ++ tailWord_7167882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167882).length < 2 ^ (prefixWord ++ tailWord_7167882).sum := by decide
  have hdescent : baseEnd_7167882 < baseStart_7167882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7167978 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7167978 : Nat := 118140960795 + 7167978 * 2 ^ 59
def prefixEnd_7167978 : Nat := 4983230072969 + 3 ^ 40 * 7167978 * 2
def baseEnd_7167978 : Nat := 3680618034853661486810075

theorem tailTrace_7167978 : CollatzResearch.WordTrace tailWord_7167978 prefixEnd_7167978 3680618034853661486810075 := by
  unfold tailWord_7167978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359408906411843506128147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174291757083764916016341725 65359408906411843506128147)
  ·
    refine ⟨98039113359617765259192221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65359408906411843506128147 98039113359617765259192221)
    ·
      refine ⟨36764667509856661972197083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98039113359617765259192221 36764667509856661972197083)
      ·
        refine ⟨55147001264784992958295625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36764667509856661972197083 55147001264784992958295625)
        ·
          refine ⟨41360250948588744718721719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55147001264784992958295625 41360250948588744718721719)
          ·
            refine ⟨62040376422883117078082579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41360250948588744718721719 62040376422883117078082579)
            ·
              refine ⟨93060564634324675617123869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62040376422883117078082579 93060564634324675617123869)
              ·
                refine ⟨34897711737871753356421451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93060564634324675617123869 34897711737871753356421451)
                ·
                  refine ⟨52346567606807630034632177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34897711737871753356421451 52346567606807630034632177)
                  ·
                    refine ⟨39259925705105722525974133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52346567606807630034632177 39259925705105722525974133)
                    ·
                      refine ⟨3680618034853661486810075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39259925705105722525974133 3680618034853661486810075)
                      ·
                        rfl

theorem cell23_7167978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7167978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7167978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7167978 prefixEnd_7167978 := by exact prefixLift 7167978
  have htrace : WordTrace (prefixWord ++ tailWord_7167978) baseStart_7167978 baseEnd_7167978 := by
    simpa [prefixWord, tailWord_7167978, baseEnd_7167978] using wordTrace_append hprefix tailTrace_7167978
  have hstable : (prefixWord ++ tailWord_7167978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7167978).length < 2 ^ (prefixWord ++ tailWord_7167978).sum := by decide
  have hdescent : baseEnd_7167978 < baseStart_7167978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7167978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168005 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_7168005 : Nat := 118140960795 + 7168005 * 2 ^ 59
def prefixEnd_7168005 : Nat := 4983230072969 + 3 ^ 40 * 7168005 * 2
def baseEnd_7168005 : Nat := 3680631898831332881172451

theorem tailTrace_7168005 : CollatzResearch.WordTrace tailWord_7168005 prefixEnd_7168005 3680631898831332881172451 := by
  unfold tailWord_7168005
  simp only [CollatzResearch.WordTrace]
  refine ⟨261438620396549557635745469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174292413597699705090496979 261438620396549557635745469)
  ·
    refine ⟨98039482648706084113404551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261438620396549557635745469 98039482648706084113404551)
    ·
      refine ⟨147059223973059126170106827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98039482648706084113404551 147059223973059126170106827)
      ·
        refine ⟨220588835959588689255160241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147059223973059126170106827 220588835959588689255160241)
        ·
          refine ⟨165441626969691516941370181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220588835959588689255160241 165441626969691516941370181)
          ·
            refine ⟨31020305056817159426506909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165441626969691516941370181 31020305056817159426506909)
            ·
              refine ⟨11632614396306434784940091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31020305056817159426506909 11632614396306434784940091)
              ·
                refine ⟨17448921594459652177410137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11632614396306434784940091 17448921594459652177410137)
                ·
                  refine ⟨13086691195844739133057603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17448921594459652177410137 13086691195844739133057603)
                  ·
                    refine ⟨19630036793767108699586405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13086691195844739133057603 19630036793767108699586405)
                    ·
                      refine ⟨3680631898831332881172451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19630036793767108699586405 3680631898831332881172451)
                      ·
                        rfl

theorem cell23_7168005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_7168005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168005 prefixEnd_7168005 := by exact prefixLift 7168005
  have htrace : WordTrace (prefixWord ++ tailWord_7168005) baseStart_7168005 baseEnd_7168005 := by
    simpa [prefixWord, tailWord_7168005, baseEnd_7168005] using wordTrace_append hprefix tailTrace_7168005
  have hstable : (prefixWord ++ tailWord_7168005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168005).length < 2 ^ (prefixWord ++ tailWord_7168005).sum := by decide
  have hdescent : baseEnd_7168005 < baseStart_7168005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168095 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 6, 2]
def baseStart_7168095 : Nat := 118140960795 + 7168095 * 2 ^ 59
def prefixEnd_7168095 : Nat := 4983230072969 + 3 ^ 40 * 7168095 * 2
def baseEnd_7168095 : Nat := 3680678112090237529047037

theorem tailTrace_7168095 : CollatzResearch.WordTrace tailWord_7168095 prefixEnd_7168095 3680678112090237529047037 := by
  unfold tailWord_7168095
  simp only [CollatzResearch.WordTrace]
  refine ⟨261441902966223503006521739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174294601977482335337681159 261441902966223503006521739)
  ·
    refine ⟨392162854449335254509782609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261441902966223503006521739 392162854449335254509782609)
    ·
      refine ⟨294122140837001440882336957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392162854449335254509782609 294122140837001440882336957)
      ·
        refine ⟨110295802813875540330876359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294122140837001440882336957 110295802813875540330876359)
        ·
          refine ⟨165443704220813310496314539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110295802813875540330876359 165443704220813310496314539)
          ·
            refine ⟨248165556331219965744471809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165443704220813310496314539 248165556331219965744471809)
            ·
              refine ⟨186124167248414974308353857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248165556331219965744471809 186124167248414974308353857)
              ·
                refine ⟨139593125436311230731265393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186124167248414974308353857 139593125436311230731265393)
                ·
                  refine ⟨104694844077233423048449045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139593125436311230731265393 104694844077233423048449045)
                  ·
                    refine ⟨4907570816120316705396049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104694844077233423048449045 4907570816120316705396049)
                    ·
                      refine ⟨3680678112090237529047037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907570816120316705396049 3680678112090237529047037)
                      ·
                        rfl

theorem cell23_7168095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_7168095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168095 prefixEnd_7168095 := by exact prefixLift 7168095
  have htrace : WordTrace (prefixWord ++ tailWord_7168095) baseStart_7168095 baseEnd_7168095 := by
    simpa [prefixWord, tailWord_7168095, baseEnd_7168095] using wordTrace_append hprefix tailTrace_7168095
  have hstable : (prefixWord ++ tailWord_7168095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168095).length < 2 ^ (prefixWord ++ tailWord_7168095).sum := by decide
  have hdescent : baseEnd_7168095 < baseStart_7168095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168112 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_7168112 : Nat := 118140960795 + 7168112 * 2 ^ 59
def prefixEnd_7168112 : Nat := 4983230072969 + 3 ^ 40 * 7168112 * 2
def baseEnd_7168112 : Nat := 3680686841261363962534459

theorem tailTrace_7168112 : CollatzResearch.WordTrace tailWord_7168112 prefixEnd_7168112 3680686841261363962534459 := by
  unfold tailWord_7168112
  simp only [CollatzResearch.WordTrace]
  refine ⟨130721261503580957454945295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174295015338107943273260393 130721261503580957454945295)
  ·
    refine ⟨196081892255371436182417943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130721261503580957454945295 196081892255371436182417943)
    ·
      refine ⟨294122838383057154273626915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196081892255371436182417943 294122838383057154273626915)
      ·
        refine ⟨441184257574585731410440373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294122838383057154273626915 441184257574585731410440373)
        ·
          refine ⟨41361024147617412319728785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 441184257574585731410440373 41361024147617412319728785)
          ·
            refine ⟨31020768110713059239796589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41361024147617412319728785 31020768110713059239796589)
            ·
              refine ⟨11632788041517397214923721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31020768110713059239796589 11632788041517397214923721)
              ·
                refine ⟨8724591031138047911192791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11632788041517397214923721 8724591031138047911192791)
                ·
                  refine ⟨13086886546707071866789187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8724591031138047911192791 13086886546707071866789187)
                  ·
                    refine ⟨19630329820060607800183781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13086886546707071866789187 19630329820060607800183781)
                    ·
                      refine ⟨3680686841261363962534459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19630329820060607800183781 3680686841261363962534459)
                      ·
                        rfl

theorem cell23_7168112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_7168112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168112 prefixEnd_7168112 := by exact prefixLift 7168112
  have htrace : WordTrace (prefixWord ++ tailWord_7168112) baseStart_7168112 baseEnd_7168112 := by
    simpa [prefixWord, tailWord_7168112, baseEnd_7168112] using wordTrace_append hprefix tailTrace_7168112
  have hstable : (prefixWord ++ tailWord_7168112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168112).length < 2 ^ (prefixWord ++ tailWord_7168112).sum := by decide
  have hdescent : baseEnd_7168112 < baseStart_7168112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168125 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_7168125 : Nat := 118140960795 + 7168125 * 2 ^ 59
def prefixEnd_7168125 : Nat := 4983230072969 + 3 ^ 40 * 7168125 * 2
def baseEnd_7168125 : Nat := 3680693516509872411671899

theorem tailTrace_7168125 : CollatzResearch.WordTrace tailWord_7168125 prefixEnd_7168125 3680693516509872411671899 := by
  unfold tailWord_7168125
  simp only [CollatzResearch.WordTrace]
  refine ⟨261442997156114818130113829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174295331437409878753409219 261442997156114818130113829)
  ·
    refine ⟨49020561966771528399396343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261442997156114818130113829 49020561966771528399396343)
    ·
      refine ⟨73530842950157292599094515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49020561966771528399396343 73530842950157292599094515)
      ·
        refine ⟨110296264425235938898641773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73530842950157292599094515 110296264425235938898641773)
        ·
          refine ⟨41361099159463477086990665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110296264425235938898641773 41361099159463477086990665)
          ·
            refine ⟨31020824369597607815242999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41361099159463477086990665 31020824369597607815242999)
            ·
              refine ⟨46531236554396411722864499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31020824369597607815242999 46531236554396411722864499)
              ·
                refine ⟨69796854831594617584296749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46531236554396411722864499 69796854831594617584296749)
                ·
                  refine ⟨26173820561847981594111281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69796854831594617584296749 26173820561847981594111281)
                  ·
                    refine ⟨19630365421385986195583461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26173820561847981594111281 19630365421385986195583461)
                    ·
                      refine ⟨3680693516509872411671899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19630365421385986195583461 3680693516509872411671899)
                      ·
                        rfl

theorem cell23_7168125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_7168125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168125 prefixEnd_7168125 := by exact prefixLift 7168125
  have htrace : WordTrace (prefixWord ++ tailWord_7168125) baseStart_7168125 baseEnd_7168125 := by
    simpa [prefixWord, tailWord_7168125, baseEnd_7168125] using wordTrace_append hprefix tailTrace_7168125
  have hstable : (prefixWord ++ tailWord_7168125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168125).length < 2 ^ (prefixWord ++ tailWord_7168125).sum := by decide
  have hdescent : baseEnd_7168125 < baseStart_7168125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168152 : List Nat := [2, 1, 2, 4, 3, 2, 1, 8]
def baseStart_7168152 : Nat := 118140960795 + 7168152 * 2 ^ 59
def prefixEnd_7168152 : Nat := 4983230072969 + 3 ^ 40 * 7168152 * 2
def baseEnd_7168152 : Nat := 136322495573612733556825

theorem tailTrace_7168152 : CollatzResearch.WordTrace tailWord_7168152 prefixEnd_7168152 136322495573612733556825 := by
  unfold tailWord_7168152
  simp only [CollatzResearch.WordTrace]
  refine ⟨130721990963508500870673355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174295987951344667827564473 130721990963508500870673355)
  ·
    refine ⟨196082986445262751306010033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130721990963508500870673355 196082986445262751306010033)
    ·
      refine ⟨147062239833947063479507525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196082986445262751306010033 147062239833947063479507525)
      ·
        refine ⟨27574169968865074402407661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147062239833947063479507525 27574169968865074402407661)
        ·
          refine ⟨10340313738324402900902873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27574169968865074402407661 10340313738324402900902873)
          ·
            refine ⟨7755235303743302175677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10340313738324402900902873 7755235303743302175677155)
            ·
              refine ⟨11632852955614953263515733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755235303743302175677155 11632852955614953263515733)
              ·
                refine ⟨136322495573612733556825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11632852955614953263515733 136322495573612733556825)
                ·
                  rfl

theorem cell23_7168152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 8].length) (baseStart_7168152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168152 prefixEnd_7168152 := by exact prefixLift 7168152
  have htrace : WordTrace (prefixWord ++ tailWord_7168152) baseStart_7168152 baseEnd_7168152 := by
    simpa [prefixWord, tailWord_7168152, baseEnd_7168152] using wordTrace_append hprefix tailTrace_7168152
  have hstable : (prefixWord ++ tailWord_7168152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168152).length < 2 ^ (prefixWord ++ tailWord_7168152).sum := by decide
  have hdescent : baseEnd_7168152 < baseStart_7168152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168196 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7168196 : Nat := 118140960795 + 7168196 * 2 ^ 59
def prefixEnd_7168196 : Nat := 4983230072969 + 3 ^ 40 * 7168196 * 2
def baseEnd_7168196 : Nat := 3680729973636341633884073

theorem tailTrace_7168196 : CollatzResearch.WordTrace tailWord_7168196 prefixEnd_7168196 3680729973636341633884073 := by
  unfold tailWord_7168196
  simp only [CollatzResearch.WordTrace]
  refine ⟨130722793369428798627974221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174297057825905064837298961 130722793369428798627974221)
  ·
    refine ⟨49021047513535799485490333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130722793369428798627974221 49021047513535799485490333)
    ·
      refine ⟨18382892817575924807058875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49021047513535799485490333 18382892817575924807058875)
      ·
        refine ⟨27574339226363887210588313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18382892817575924807058875 27574339226363887210588313)
        ·
          refine ⟨20680754419772915407941235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27574339226363887210588313 20680754419772915407941235)
          ·
            refine ⟨31021131629659373111911853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20680754419772915407941235 31021131629659373111911853)
            ·
              refine ⟨11632924361122264916966945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31021131629659373111911853 11632924361122264916966945)
              ·
                refine ⟨8724693270841698687725209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11632924361122264916966945 8724693270841698687725209)
                ·
                  refine ⟨6543519953131274015793907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8724693270841698687725209 6543519953131274015793907)
                  ·
                    refine ⟨9815279929696911023690861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543519953131274015793907 9815279929696911023690861)
                    ·
                      refine ⟨3680729973636341633884073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815279929696911023690861 3680729973636341633884073)
                      ·
                        rfl

theorem cell23_7168196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7168196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168196 prefixEnd_7168196 := by exact prefixLift 7168196
  have htrace : WordTrace (prefixWord ++ tailWord_7168196) baseStart_7168196 baseEnd_7168196 := by
    simpa [prefixWord, tailWord_7168196, baseEnd_7168196] using wordTrace_append hprefix tailTrace_7168196
  have hstable : (prefixWord ++ tailWord_7168196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168196).length < 2 ^ (prefixWord ++ tailWord_7168196).sum := by decide
  have hdescent : baseEnd_7168196 < baseStart_7168196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168213 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7168213 : Nat := 118140960795 + 7168213 * 2 ^ 59
def prefixEnd_7168213 : Nat := 4983230072969 + 3 ^ 40 * 7168213 * 2
def baseEnd_7168213 : Nat := 3680738702807468067371495

theorem tailTrace_7168213 : CollatzResearch.WordTrace tailWord_7168213 prefixEnd_7168213 3680738702807468067371495 := by
  unfold tailWord_7168213
  simp only [CollatzResearch.WordTrace]
  refine ⟨261446206779796009159317293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174297471186530672772878195 261446206779796009159317293)
  ·
    refine ⟨98042327542423503434743985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261446206779796009159317293 98042327542423503434743985)
    ·
      refine ⟨73531745656817627576057989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98042327542423503434743985 73531745656817627576057989)
      ·
        refine ⟨13787202310653305170510873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73531745656817627576057989 13787202310653305170510873)
        ·
          refine ⟨10340401732989978877883155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13787202310653305170510873 10340401732989978877883155)
          ·
            refine ⟨15510602599484968316824733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340401732989978877883155 15510602599484968316824733)
            ·
              refine ⟨5816475974806863118809275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15510602599484968316824733 5816475974806863118809275)
              ·
                refine ⟨8724713962210294678213913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816475974806863118809275 8724713962210294678213913)
                ·
                  refine ⟨6543535471657721008660435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8724713962210294678213913 6543535471657721008660435)
                  ·
                    refine ⟨9815303207486581512990653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543535471657721008660435 9815303207486581512990653)
                    ·
                      refine ⟨3680738702807468067371495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815303207486581512990653 3680738702807468067371495)
                      ·
                        rfl

theorem cell23_7168213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7168213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168213 prefixEnd_7168213 := by exact prefixLift 7168213
  have htrace : WordTrace (prefixWord ++ tailWord_7168213) baseStart_7168213 baseEnd_7168213 := by
    simpa [prefixWord, tailWord_7168213, baseEnd_7168213] using wordTrace_append hprefix tailTrace_7168213
  have hstable : (prefixWord ++ tailWord_7168213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168213).length < 2 ^ (prefixWord ++ tailWord_7168213).sum := by decide
  have hdescent : baseEnd_7168213 < baseStart_7168213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168225 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 7]
def baseStart_7168225 : Nat := 118140960795 + 7168225 * 2 ^ 59
def prefixEnd_7168225 : Nat := 4983230072969 + 3 ^ 40 * 7168225 * 2
def baseEnd_7168225 : Nat := 408971651619480224491271

theorem tailTrace_7168225 : CollatzResearch.WordTrace tailWord_7168225 prefixEnd_7168225 408971651619480224491271 := by
  unfold tailWord_7168225
  simp only [CollatzResearch.WordTrace]
  refine ⟨261446644455752535208754129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174297762970501690139169419 261446644455752535208754129)
  ·
    refine ⟨196084983341814401406565597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261446644455752535208754129 196084983341814401406565597)
    ·
      refine ⟨73531868753180400527462099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196084983341814401406565597 73531868753180400527462099)
      ·
        refine ⟨110297803129770600791193149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73531868753180400527462099 110297803129770600791193149)
        ·
          refine ⟨41361676173663975296697431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110297803129770600791193149 41361676173663975296697431)
          ·
            refine ⟨62042514260495962945046147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41361676173663975296697431 62042514260495962945046147)
            ·
              refine ⟨93063771390743944417569221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62042514260495962945046147 93063771390743944417569221)
              ·
                refine ⟨17449457135764489578294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93063771390743944417569221 17449457135764489578294229)
                ·
                  refine ⟨408971651619480224491271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17449457135764489578294229 408971651619480224491271)
                  ·
                    rfl

theorem cell23_7168225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_7168225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168225 prefixEnd_7168225 := by exact prefixLift 7168225
  have htrace : WordTrace (prefixWord ++ tailWord_7168225) baseStart_7168225 baseEnd_7168225 := by
    simpa [prefixWord, tailWord_7168225, baseEnd_7168225] using wordTrace_append hprefix tailTrace_7168225
  have hstable : (prefixWord ++ tailWord_7168225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168225).length < 2 ^ (prefixWord ++ tailWord_7168225).sum := by decide
  have hdescent : baseEnd_7168225 < baseStart_7168225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168259 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 5]
def baseStart_7168259 : Nat := 118140960795 + 7168259 * 2 ^ 59
def prefixEnd_7168259 : Nat := 4983230072969 + 3 ^ 40 * 7168259 * 2
def baseEnd_7168259 : Nat := 408973591435286098599587

theorem tailTrace_7168259 : CollatzResearch.WordTrace tailWord_7168259 prefixEnd_7168259 408973591435286098599587 := by
  unfold tailWord_7168259
  simp only [CollatzResearch.WordTrace]
  refine ⟨261447884537629359015491831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174298589691752906010327887 261447884537629359015491831)
  ·
    refine ⟨392171826806444038523237747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261447884537629359015491831 392171826806444038523237747)
    ·
      refine ⟨588257740209666057784856621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392171826806444038523237747 588257740209666057784856621)
      ·
        refine ⟨220596652578624771669321233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588257740209666057784856621 220596652578624771669321233)
        ·
          refine ⟨165447489433968578751990925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220596652578624771669321233 165447489433968578751990925)
          ·
            refine ⟨62042808537738217031996597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165447489433968578751990925 62042808537738217031996597)
            ·
              refine ⟨5816513300412957846749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62042808537738217031996597 5816513300412957846749681)
              ·
                refine ⟨4362384975309718385062261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816513300412957846749681 4362384975309718385062261)
                ·
                  refine ⟨408973591435286098599587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362384975309718385062261 408973591435286098599587)
                  ·
                    rfl

theorem cell23_7168259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 5].length) (baseStart_7168259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168259 prefixEnd_7168259 := by exact prefixLift 7168259
  have htrace : WordTrace (prefixWord ++ tailWord_7168259) baseStart_7168259 baseEnd_7168259 := by
    simpa [prefixWord, tailWord_7168259, baseEnd_7168259] using wordTrace_append hprefix tailTrace_7168259
  have hstable : (prefixWord ++ tailWord_7168259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168259).length < 2 ^ (prefixWord ++ tailWord_7168259).sum := by decide
  have hdescent : baseEnd_7168259 < baseStart_7168259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168265 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_7168265 : Nat := 118140960795 + 7168265 * 2 ^ 59
def prefixEnd_7168265 : Nat := 4983230072969 + 3 ^ 40 * 7168265 * 2
def baseEnd_7168265 : Nat := 3680765403801501863921255

theorem tailTrace_7168265 : CollatzResearch.WordTrace tailWord_7168265 prefixEnd_7168265 3680765403801501863921255 := by
  unfold tailWord_7168265
  simp only [CollatzResearch.WordTrace]
  refine ⟨261448103375607622040210249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174298735583738414693473499 261448103375607622040210249)
  ·
    refine ⟨196086077531705716530157687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261448103375607622040210249 196086077531705716530157687)
    ·
      refine ⟨294129116297558574795236531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196086077531705716530157687 294129116297558574795236531)
      ·
        refine ⟨441193674446337862192854797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294129116297558574795236531 441193674446337862192854797)
        ·
          refine ⟨165447627917376698322320549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441193674446337862192854797 165447627917376698322320549)
          ·
            refine ⟨31021430234508130935435103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165447627917376698322320549 31021430234508130935435103)
            ·
              refine ⟨46532145351762196403152655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31021430234508130935435103 46532145351762196403152655)
              ·
                refine ⟨69798218027643294604728983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46532145351762196403152655 69798218027643294604728983)
                ·
                  refine ⟨104697327041464941907093475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69798218027643294604728983 104697327041464941907093475)
                  ·
                    refine ⟨157045990562197412860640213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104697327041464941907093475 157045990562197412860640213)
                    ·
                      refine ⟨3680765403801501863921255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157045990562197412860640213 3680765403801501863921255)
                      ·
                        rfl

theorem cell23_7168265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_7168265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168265 prefixEnd_7168265 := by exact prefixLift 7168265
  have htrace : WordTrace (prefixWord ++ tailWord_7168265) baseStart_7168265 baseEnd_7168265 := by
    simpa [prefixWord, tailWord_7168265, baseEnd_7168265] using wordTrace_append hprefix tailTrace_7168265
  have hstable : (prefixWord ++ tailWord_7168265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168265).length < 2 ^ (prefixWord ++ tailWord_7168265).sum := by decide
  have hdescent : baseEnd_7168265 < baseStart_7168265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168275 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_7168275 : Nat := 118140960795 + 7168275 * 2 ^ 59
def prefixEnd_7168275 : Nat := 4983230072969 + 3 ^ 40 * 7168275 * 2
def baseEnd_7168275 : Nat := 3680770538608046824796209

theorem tailTrace_7168275 : CollatzResearch.WordTrace tailWord_7168275 prefixEnd_7168275 3680770538608046824796209 := by
  unfold tailWord_7168275
  simp only [CollatzResearch.WordTrace]
  refine ⟨261448468105571393748074279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174298978737047595832049519 261448468105571393748074279)
  ·
    refine ⟨392172702158357090622111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261448468105571393748074279 392172702158357090622111419)
    ·
      refine ⟨588259053237535635933167129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392172702158357090622111419 588259053237535635933167129)
      ·
        refine ⟨441194289928151726949875347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588259053237535635933167129 441194289928151726949875347)
        ·
          refine ⟨661791434892227590424813021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441194289928151726949875347 661791434892227590424813021)
          ·
            refine ⟨248171788084585346409304883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661791434892227590424813021 248171788084585346409304883)
            ·
              refine ⟨372257682126878019613957325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248171788084585346409304883 372257682126878019613957325)
              ·
                refine ⟨139596630797579257355233997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372257682126878019613957325 139596630797579257355233997)
                ·
                  refine ⟨52348736549092221508212749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139596630797579257355233997 52348736549092221508212749)
                  ·
                    refine ⟨19630776205909583065579781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52348736549092221508212749 19630776205909583065579781)
                    ·
                      refine ⟨3680770538608046824796209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19630776205909583065579781 3680770538608046824796209)
                      ·
                        rfl

theorem cell23_7168275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_7168275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168275 prefixEnd_7168275 := by exact prefixLift 7168275
  have htrace : WordTrace (prefixWord ++ tailWord_7168275) baseStart_7168275 baseEnd_7168275 := by
    simpa [prefixWord, tailWord_7168275, baseEnd_7168275] using wordTrace_append hprefix tailTrace_7168275
  have hstable : (prefixWord ++ tailWord_7168275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168275).length < 2 ^ (prefixWord ++ tailWord_7168275).sum := by decide
  have hdescent : baseEnd_7168275 < baseStart_7168275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168309 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_7168309 : Nat := 118140960795 + 7168309 * 2 ^ 59
def prefixEnd_7168309 : Nat := 4983230072969 + 3 ^ 40 * 7168309 * 2
def baseEnd_7168309 : Nat := 3680787996950299691771053

theorem tailTrace_7168309 : CollatzResearch.WordTrace tailWord_7168309 prefixEnd_7168309 3680787996950299691771053 := by
  unfold tailWord_7168309
  simp only [CollatzResearch.WordTrace]
  refine ⟨261449708187448217554811981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174299805458298811703207987 261449708187448217554811981)
  ·
    refine ⟨98043640570293081583054493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261449708187448217554811981 98043640570293081583054493)
    ·
      refine ⟨36766365213859905593645435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98043640570293081583054493 36766365213859905593645435)
      ·
        refine ⟨55149547820789858390468153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36766365213859905593645435 55149547820789858390468153)
        ·
          refine ⟨41362160865592393792851115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55149547820789858390468153 41362160865592393792851115)
          ·
            refine ⟨62043241298388590689276673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41362160865592393792851115 62043241298388590689276673)
            ·
              refine ⟨46532430973791443016957505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62043241298388590689276673 46532430973791443016957505)
              ·
                refine ⟨34899323230343582262718129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46532430973791443016957505 34899323230343582262718129)
                ·
                  refine ⟨26174492422757686697038597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34899323230343582262718129 26174492422757686697038597)
                  ·
                    refine ⟨4907717329267066255694737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26174492422757686697038597 4907717329267066255694737)
                    ·
                      refine ⟨3680787996950299691771053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907717329267066255694737 3680787996950299691771053)
                      ·
                        rfl

theorem cell23_7168309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_7168309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168309 prefixEnd_7168309 := by exact prefixLift 7168309
  have htrace : WordTrace (prefixWord ++ tailWord_7168309) baseStart_7168309 baseEnd_7168309 := by
    simpa [prefixWord, tailWord_7168309, baseEnd_7168309] using wordTrace_append hprefix tailTrace_7168309
  have hstable : (prefixWord ++ tailWord_7168309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168309).length < 2 ^ (prefixWord ++ tailWord_7168309).sum := by decide
  have hdescent : baseEnd_7168309 < baseStart_7168309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168332 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 6]
def baseStart_7168332 : Nat := 118140960795 + 7168332 * 2 ^ 59
def prefixEnd_7168332 : Nat := 4983230072969 + 3 ^ 40 * 7168332 * 2
def baseEnd_7168332 : Nat := 408977756333928122420383

theorem tailTrace_7168332 : CollatzResearch.WordTrace tailWord_7168332 prefixEnd_7168332 408977756333928122420383 := by
  unfold tailWord_7168332
  simp only [CollatzResearch.WordTrace]
  refine ⟨130725273533182446241449625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174300364710909928321932833 130725273533182446241449625)
  ·
    refine ⟨98043955149886834681087219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130725273533182446241449625 98043955149886834681087219)
    ·
      refine ⟨147065932724830252021630829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98043955149886834681087219 147065932724830252021630829)
      ·
        refine ⟨55149724771811344508111561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147065932724830252021630829 55149724771811344508111561)
        ·
          refine ⟨41362293578858508381083671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55149724771811344508111561 41362293578858508381083671)
          ·
            refine ⟨62043440368287762571625507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41362293578858508381083671 62043440368287762571625507)
            ·
              refine ⟨93065160552431643857438261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62043440368287762571625507 93065160552431643857438261)
              ·
                refine ⟨8724858801790466611634837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93065160552431643857438261 8724858801790466611634837)
                ·
                  refine ⟨408977756333928122420383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8724858801790466611634837 408977756333928122420383)
                  ·
                    rfl

theorem cell23_7168332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_7168332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168332 prefixEnd_7168332 := by exact prefixLift 7168332
  have htrace : WordTrace (prefixWord ++ tailWord_7168332) baseStart_7168332 baseEnd_7168332 := by
    simpa [prefixWord, tailWord_7168332, baseEnd_7168332] using wordTrace_append hprefix tailTrace_7168332
  have hstable : (prefixWord ++ tailWord_7168332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168332).length < 2 ^ (prefixWord ++ tailWord_7168332).sum := by decide
  have hdescent : baseEnd_7168332 < baseStart_7168332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_7168335 : Nat := 118140960795 + 7168335 * 2 ^ 59
def prefixEnd_7168335 : Nat := 4983230072969 + 3 ^ 40 * 7168335 * 2
def baseEnd_7168335 : Nat := 3680801347447316590045933

theorem tailTrace_7168335 : CollatzResearch.WordTrace tailWord_7168335 prefixEnd_7168335 3680801347447316590045933 := by
  unfold tailWord_7168335
  simp only [CollatzResearch.WordTrace]
  refine ⟨261450656485354023995258459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174300437656902682663505639 261450656485354023995258459)
  ·
    refine ⟨392175984728031035992887689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261450656485354023995258459 392175984728031035992887689)
    ·
      refine ⟨294131988546023276994665767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392175984728031035992887689 294131988546023276994665767)
      ·
        refine ⟨441197982819034915491998651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294131988546023276994665767 441197982819034915491998651)
        ·
          refine ⟨661796974228552373237997977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441197982819034915491998651 661796974228552373237997977)
          ·
            refine ⟨496347730671414279928498483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661796974228552373237997977 496347730671414279928498483)
            ·
              refine ⟨744521596007121419892747725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496347730671414279928498483 744521596007121419892747725)
              ·
                refine ⟨279195598502670532459780397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 744521596007121419892747725 279195598502670532459780397)
                ·
                  refine ⟨104698349438501449672417649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279195598502670532459780397 104698349438501449672417649)
                  ·
                    refine ⟨78523762078876087254313237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104698349438501449672417649 78523762078876087254313237)
                    ·
                      refine ⟨3680801347447316590045933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78523762078876087254313237 3680801347447316590045933)
                      ·
                        rfl

theorem cell23_7168335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_7168335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168335 prefixEnd_7168335 := by exact prefixLift 7168335
  have htrace : WordTrace (prefixWord ++ tailWord_7168335) baseStart_7168335 baseEnd_7168335 := by
    simpa [prefixWord, tailWord_7168335, baseEnd_7168335] using wordTrace_append hprefix tailTrace_7168335
  have hstable : (prefixWord ++ tailWord_7168335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168335).length < 2 ^ (prefixWord ++ tailWord_7168335).sum := by decide
  have hdescent : baseEnd_7168335 < baseStart_7168335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_7168369 : Nat := 118140960795 + 7168369 * 2 ^ 59
def prefixEnd_7168369 : Nat := 4983230072969 + 3 ^ 40 * 7168369 * 2
def baseEnd_7168369 : Nat := 3680818805789569457020777

theorem tailTrace_7168369 : CollatzResearch.WordTrace tailWord_7168369 prefixEnd_7168369 3680818805789569457020777 := by
  unfold tailWord_7168369
  simp only [CollatzResearch.WordTrace]
  refine ⟨261451896567230847801996161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174301264378153898534664107 261451896567230847801996161)
  ·
    refine ⟨196088922425423135851497121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261451896567230847801996161 196088922425423135851497121)
    ·
      refine ⟨147066691819067351888622841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196088922425423135851497121 147066691819067351888622841)
      ·
        refine ⟨110300018864300513916467131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147066691819067351888622841 110300018864300513916467131)
        ·
          refine ⟨165450028296450770874700697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110300018864300513916467131 165450028296450770874700697)
          ·
            refine ⟨124087521222338078156025523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165450028296450770874700697 124087521222338078156025523)
            ·
              refine ⟨186131281833507117234038285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124087521222338078156025523 186131281833507117234038285)
              ·
                refine ⟨69799230687565168962764357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186131281833507117234038285 69799230687565168962764357)
                ·
                  refine ⟨13087355753918469180518317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69799230687565168962764357 13087355753918469180518317)
                  ·
                    refine ⟨4907758407719425942694369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13087355753918469180518317 4907758407719425942694369)
                    ·
                      refine ⟨3680818805789569457020777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907758407719425942694369 3680818805789569457020777)
                      ·
                        rfl

theorem cell23_7168369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_7168369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168369 prefixEnd_7168369 := by exact prefixLift 7168369
  have htrace : WordTrace (prefixWord ++ tailWord_7168369) baseStart_7168369 baseEnd_7168369 := by
    simpa [prefixWord, tailWord_7168369, baseEnd_7168369] using wordTrace_append hprefix tailTrace_7168369
  have hstable : (prefixWord ++ tailWord_7168369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168369).length < 2 ^ (prefixWord ++ tailWord_7168369).sum := by decide
  have hdescent : baseEnd_7168369 < baseStart_7168369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168410 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7168410 : Nat := 118140960795 + 7168410 * 2 ^ 59
def prefixEnd_7168410 : Nat := 4983230072969 + 3 ^ 40 * 7168410 * 2
def baseEnd_7168410 : Nat := 3680839858496403796608089

theorem tailTrace_7168410 : CollatzResearch.WordTrace tailWord_7168410 prefixEnd_7168410 3680839858496403796608089 := by
  unfold tailWord_7168410
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363347990020577951059671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174302261306721541202825789 65363347990020577951059671)
  ·
    refine ⟨98045021985030866926589507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65363347990020577951059671 98045021985030866926589507)
    ·
      refine ⟨147067532977546300389884261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98045021985030866926589507 147067532977546300389884261)
      ·
        refine ⟨27575162433289931323103299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147067532977546300389884261 27575162433289931323103299)
        ·
          refine ⟨41362743649934896984654949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27575162433289931323103299 41362743649934896984654949)
          ·
            refine ⟨7755514434362793184622803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41362743649934896984654949 7755514434362793184622803)
            ·
              refine ⟨11633271651544189776934205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755514434362793184622803 11633271651544189776934205)
              ·
                refine ⟨4362476869329071166350327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633271651544189776934205 4362476869329071166350327)
                ·
                  refine ⟨6543715303993606749525491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362476869329071166350327 6543715303993606749525491)
                  ·
                    refine ⟨9815572955990410124288237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543715303993606749525491 9815572955990410124288237)
                    ·
                      refine ⟨3680839858496403796608089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815572955990410124288237 3680839858496403796608089)
                      ·
                        rfl

theorem cell23_7168410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7168410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168410 prefixEnd_7168410 := by exact prefixLift 7168410
  have htrace : WordTrace (prefixWord ++ tailWord_7168410) baseStart_7168410 baseEnd_7168410 := by
    simpa [prefixWord, tailWord_7168410, baseEnd_7168410] using wordTrace_append hprefix tailTrace_7168410
  have hstable : (prefixWord ++ tailWord_7168410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168410).length < 2 ^ (prefixWord ++ tailWord_7168410).sum := by decide
  have hdescent : baseEnd_7168410 < baseStart_7168410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168419 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5]
def baseStart_7168419 : Nat := 118140960795 + 7168419 * 2 ^ 59
def prefixEnd_7168419 : Nat := 4983230072969 + 3 ^ 40 * 7168419 * 2
def baseEnd_7168419 : Nat := 3680844479822294261395547

theorem tailTrace_7168419 : CollatzResearch.WordTrace tailWord_7168419 prefixEnd_7168419 3680844479822294261395547 := by
  unfold tailWord_7168419
  simp only [CollatzResearch.WordTrace]
  refine ⟨261453720217049706341316311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174302480144699804227544207 261453720217049706341316311)
  ·
    refine ⟨392180580325574559511974467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261453720217049706341316311 392180580325574559511974467)
    ·
      refine ⟨588270870488361839267961701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392180580325574559511974467 588270870488361839267961701)
      ·
        refine ⟨110300788216567844862742819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588270870488361839267961701 110300788216567844862742819)
        ·
          refine ⟨165451182324851767294114229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110300788216567844862742819 165451182324851767294114229)
          ·
            refine ⟨15511048342954853183823209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165451182324851767294114229 15511048342954853183823209)
            ·
              refine ⟨11633286257216139887867407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511048342954853183823209 11633286257216139887867407)
              ·
                refine ⟨17449929385824209831801111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633286257216139887867407 17449929385824209831801111)
                ·
                  refine ⟨26174894078736314747701667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17449929385824209831801111 26174894078736314747701667)
                  ·
                    refine ⟨39262341118104472121552501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26174894078736314747701667 39262341118104472121552501)
                    ·
                      refine ⟨3680844479822294261395547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39262341118104472121552501 3680844479822294261395547)
                      ·
                        rfl

theorem cell23_7168419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_7168419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168419 prefixEnd_7168419 := by exact prefixLift 7168419
  have htrace : WordTrace (prefixWord ++ tailWord_7168419) baseStart_7168419 baseEnd_7168419 := by
    simpa [prefixWord, tailWord_7168419, baseEnd_7168419] using wordTrace_append hprefix tailTrace_7168419
  have hstable : (prefixWord ++ tailWord_7168419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168419).length < 2 ^ (prefixWord ++ tailWord_7168419).sum := by decide
  have hdescent : baseEnd_7168419 < baseStart_7168419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168433 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7168433 : Nat := 118140960795 + 7168433 * 2 ^ 59
def prefixEnd_7168433 : Nat := 4983230072969 + 3 ^ 40 * 7168433 * 2
def baseEnd_7168433 : Nat := 3680851668551457206620483

theorem tailTrace_7168433 : CollatzResearch.WordTrace tailWord_7168433 prefixEnd_7168433 3680851668551457206620483 := by
  unfold tailWord_7168433
  simp only [CollatzResearch.WordTrace]
  refine ⟨261454230838998986732325953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174302820559332657821550635 261454230838998986732325953)
  ·
    refine ⟨196090673129249240049244465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261454230838998986732325953 196090673129249240049244465)
    ·
      refine ⟨147068004846936930036933349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196090673129249240049244465 147068004846936930036933349)
      ·
        refine ⟨27575250908800674381925003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147068004846936930036933349 27575250908800674381925003)
        ·
          refine ⟨41362876363201011572887505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27575250908800674381925003 41362876363201011572887505)
          ·
            refine ⟨31022157272400758679665629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41362876363201011572887505 31022157272400758679665629)
            ·
              refine ⟨11633308977150284504874611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31022157272400758679665629 11633308977150284504874611)
              ·
                refine ⟨17449963465725426757311917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633308977150284504874611 17449963465725426757311917)
                ·
                  refine ⟨6543736299647035033991969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17449963465725426757311917 6543736299647035033991969)
                  ·
                    refine ⟨4907802224735276275493977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543736299647035033991969 4907802224735276275493977)
                    ·
                      refine ⟨3680851668551457206620483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907802224735276275493977 3680851668551457206620483)
                      ·
                        rfl

theorem cell23_7168433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7168433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168433 prefixEnd_7168433 := by exact prefixLift 7168433
  have htrace : WordTrace (prefixWord ++ tailWord_7168433) baseStart_7168433 baseEnd_7168433 := by
    simpa [prefixWord, tailWord_7168433, baseEnd_7168433] using wordTrace_append hprefix tailTrace_7168433
  have hstable : (prefixWord ++ tailWord_7168433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168433).length < 2 ^ (prefixWord ++ tailWord_7168433).sum := by decide
  have hdescent : baseEnd_7168433 < baseStart_7168433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168470 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7168470 : Nat := 118140960795 + 7168470 * 2 ^ 59
def prefixEnd_7168470 : Nat := 4983230072969 + 3 ^ 40 * 7168470 * 2
def baseEnd_7168470 : Nat := 3680870667335673561857813

theorem tailTrace_7168470 : CollatzResearch.WordTrace tailWord_7168470 prefixEnd_7168470 3680870667335673561857813 := by
  unfold tailWord_7168470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340973771241558878213929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174303720226576628034281909 16340973771241558878213929)
  ·
    refine ⟨12255730328431169158660447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16340973771241558878213929 12255730328431169158660447)
    ·
      refine ⟨18383595492646753737990671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255730328431169158660447 18383595492646753737990671)
      ·
        refine ⟨27575393238970130606986007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383595492646753737990671 27575393238970130606986007)
        ·
          refine ⟨41363089858455195910479011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27575393238970130606986007 41363089858455195910479011)
          ·
            refine ⟨62044634787682793865718517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41363089858455195910479011 62044634787682793865718517)
            ·
              refine ⟨5816684511345261924911111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62044634787682793865718517 5816684511345261924911111)
              ·
                refine ⟨8725026767017892887366667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816684511345261924911111 8725026767017892887366667)
                ·
                  refine ⟨13087540150526839331050001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725026767017892887366667 13087540150526839331050001)
                  ·
                    refine ⟨9815655112895129498287501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13087540150526839331050001 9815655112895129498287501)
                    ·
                      refine ⟨3680870667335673561857813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815655112895129498287501 3680870667335673561857813)
                      ·
                        rfl

theorem cell23_7168470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7168470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168470 prefixEnd_7168470 := by exact prefixLift 7168470
  have htrace : WordTrace (prefixWord ++ tailWord_7168470) baseStart_7168470 baseEnd_7168470 := by
    simpa [prefixWord, tailWord_7168470, baseEnd_7168470] using wordTrace_append hprefix tailTrace_7168470
  have hstable : (prefixWord ++ tailWord_7168470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168470).length < 2 ^ (prefixWord ++ tailWord_7168470).sum := by decide
  have hdescent : baseEnd_7168470 < baseStart_7168470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168493 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7168493 : Nat := 118140960795 + 7168493 * 2 ^ 59
def prefixEnd_7168493 : Nat := 4983230072969 + 3 ^ 40 * 7168493 * 2
def baseEnd_7168493 : Nat := 3680882477390726971870207

theorem tailTrace_7168493 : CollatzResearch.WordTrace tailWord_7168493 prefixEnd_7168493 3680882477390726971870207 := by
  unfold tailWord_7168493
  simp only [CollatzResearch.WordTrace]
  refine ⟨261456419218781616979510133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174304279479187744653006755 261456419218781616979510133)
  ·
    refine ⟨24511539301760776591829075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261456419218781616979510133 24511539301760776591829075)
    ·
      refine ⟨36767308952641164887743613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24511539301760776591829075 36767308952641164887743613)
      ·
        refine ⟨13787740857240436832903855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36767308952641164887743613 13787740857240436832903855)
        ·
          refine ⟨20681611285860655249355783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787740857240436832903855 20681611285860655249355783)
          ·
            refine ⟨31022416928790982874033675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20681611285860655249355783 31022416928790982874033675)
            ·
              refine ⟨46533625393186474311050513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31022416928790982874033675 46533625393186474311050513)
              ·
                refine ⟨34900219044889855733287885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46533625393186474311050513 34900219044889855733287885)
                ·
                  refine ⟨13087582141833695899982957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34900219044889855733287885 13087582141833695899982957)
                  ·
                    refine ⟨4907843303187635962493609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13087582141833695899982957 4907843303187635962493609)
                    ·
                      refine ⟨3680882477390726971870207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907843303187635962493609 3680882477390726971870207)
                      ·
                        rfl

theorem cell23_7168493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7168493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168493 prefixEnd_7168493 := by exact prefixLift 7168493
  have htrace : WordTrace (prefixWord ++ tailWord_7168493) baseStart_7168493 baseEnd_7168493 := by
    simpa [prefixWord, tailWord_7168493, baseEnd_7168493] using wordTrace_append hprefix tailTrace_7168493
  have hstable : (prefixWord ++ tailWord_7168493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168493).length < 2 ^ (prefixWord ++ tailWord_7168493).sum := by decide
  have hdescent : baseEnd_7168493 < baseStart_7168493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168509 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_7168509 : Nat := 118140960795 + 7168509 * 2 ^ 59
def prefixEnd_7168509 : Nat := 4983230072969 + 3 ^ 40 * 7168509 * 2
def baseEnd_7168509 : Nat := 3680890693081198909270133

theorem tailTrace_7168509 : CollatzResearch.WordTrace tailWord_7168509 prefixEnd_7168509 3680890693081198909270133 := by
  unfold tailWord_7168509
  simp only [CollatzResearch.WordTrace]
  refine ⟨261457002786723651712092581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174304668524482434474728387 261457002786723651712092581)
  ·
    refine ⟨49023188022510684696017359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261457002786723651712092581 49023188022510684696017359)
    ·
      refine ⟨73534782033766027044026039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49023188022510684696017359 73534782033766027044026039)
      ·
        refine ⟨110302173050649040566039059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73534782033766027044026039 110302173050649040566039059)
        ·
          refine ⟨165453259575973560849058589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110302173050649040566039059 165453259575973560849058589)
          ·
            refine ⟨62044972340990085318396971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165453259575973560849058589 62044972340990085318396971)
            ·
              refine ⟨93067458511485127977595457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62044972340990085318396971 93067458511485127977595457)
              ·
                refine ⟨69800593883613845983196593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93067458511485127977595457 69800593883613845983196593)
                ·
                  refine ⟨52350445412710384487397445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69800593883613845983196593 52350445412710384487397445)
                  ·
                    refine ⟨9815708514883197091387021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52350445412710384487397445 9815708514883197091387021)
                    ·
                      refine ⟨3680890693081198909270133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815708514883197091387021 3680890693081198909270133)
                      ·
                        rfl

theorem cell23_7168509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_7168509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168509 prefixEnd_7168509 := by exact prefixLift 7168509
  have htrace : WordTrace (prefixWord ++ tailWord_7168509) baseStart_7168509 baseEnd_7168509 := by
    simpa [prefixWord, tailWord_7168509, baseEnd_7168509] using wordTrace_append hprefix tailTrace_7168509
  have hstable : (prefixWord ++ tailWord_7168509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168509).length < 2 ^ (prefixWord ++ tailWord_7168509).sum := by decide
  have hdescent : baseEnd_7168509 < baseStart_7168509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168540 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7168540 : Nat := 118140960795 + 7168540 * 2 ^ 59
def prefixEnd_7168540 : Nat := 4983230072969 + 3 ^ 40 * 7168540 * 2
def baseEnd_7168540 : Nat := 3680906610981488287982491

theorem tailTrace_7168540 : CollatzResearch.WordTrace tailWord_7168540 prefixEnd_7168540 3680906610981488287982491 := by
  unfold tailWord_7168540
  simp only [CollatzResearch.WordTrace]
  refine ⟨130729066724805672003235537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174305422299740896004314049 130729066724805672003235537)
  ·
    refine ⟨98046800043604254002426653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130729066724805672003235537 98046800043604254002426653)
    ·
      refine ⟨36767550016351595250909995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98046800043604254002426653 36767550016351595250909995)
      ·
        refine ⟨55151325024527392876364993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36767550016351595250909995 55151325024527392876364993)
        ·
          refine ⟨41363493768395544657273745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55151325024527392876364993 41363493768395544657273745)
          ·
            refine ⟨31022620326296658492955309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41363493768395544657273745 31022620326296658492955309)
            ·
              refine ⟨11633482622361246934858241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31022620326296658492955309 11633482622361246934858241)
              ·
                refine ⟨8725111966770935201143681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11633482622361246934858241 8725111966770935201143681)
                ·
                  refine ⟨6543833975078201400857761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725111966770935201143681 6543833975078201400857761)
                  ·
                    refine ⟨4907875481308651050643321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543833975078201400857761 4907875481308651050643321)
                    ·
                      refine ⟨3680906610981488287982491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907875481308651050643321 3680906610981488287982491)
                      ·
                        rfl

theorem cell23_7168540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7168540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168540 prefixEnd_7168540 := by exact prefixLift 7168540
  have htrace : WordTrace (prefixWord ++ tailWord_7168540) baseStart_7168540 baseEnd_7168540 := by
    simpa [prefixWord, tailWord_7168540, baseEnd_7168540] using wordTrace_append hprefix tailTrace_7168540
  have hstable : (prefixWord ++ tailWord_7168540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168540).length < 2 ^ (prefixWord ++ tailWord_7168540).sum := by decide
  have hdescent : baseEnd_7168540 < baseStart_7168540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168579 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4]
def baseStart_7168579 : Nat := 118140960795 + 7168579 * 2 ^ 59
def prefixEnd_7168579 : Nat := 4983230072969 + 3 ^ 40 * 7168579 * 2
def baseEnd_7168579 : Nat := 3680926636727013635394811

theorem tailTrace_7168579 : CollatzResearch.WordTrace tailWord_7168579 prefixEnd_7168579 3680926636727013635394811 := by
  unfold tailWord_7168579
  simp only [CollatzResearch.WordTrace]
  refine ⟨261459555896470053667140791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174306370597646702444760527 261459555896470053667140791)
  ·
    refine ⟨392189333844705080500711187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261459555896470053667140791 392189333844705080500711187)
    ·
      refine ⟨588284000767057620751066781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392189333844705080500711187 588284000767057620751066781)
      ·
        refine ⟨220606500287646607781650043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588284000767057620751066781 220606500287646607781650043)
        ·
          refine ⟨330909750431469911672475065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220606500287646607781650043 330909750431469911672475065)
          ·
            refine ⟨248182312823602433754356299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330909750431469911672475065 248182312823602433754356299)
            ·
              refine ⟨372273469235403650631534449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248182312823602433754356299 372273469235403650631534449)
              ·
                refine ⟨279205101926552737973650837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372273469235403650631534449 279205101926552737973650837)
                ·
                  refine ⟨13087739152807159592514883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279205101926552737973650837 13087739152807159592514883)
                  ·
                    refine ⟨19631608729210739388772325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13087739152807159592514883 19631608729210739388772325)
                    ·
                      refine ⟨3680926636727013635394811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19631608729210739388772325 3680926636727013635394811)
                      ·
                        rfl

theorem cell23_7168579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_7168579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168579 prefixEnd_7168579 := by exact prefixLift 7168579
  have htrace : WordTrace (prefixWord ++ tailWord_7168579) baseStart_7168579 baseEnd_7168579 := by
    simpa [prefixWord, tailWord_7168579, baseEnd_7168579] using wordTrace_append hprefix tailTrace_7168579
  have hstable : (prefixWord ++ tailWord_7168579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168579).length < 2 ^ (prefixWord ++ tailWord_7168579).sum := by decide
  have hdescent : baseEnd_7168579 < baseStart_7168579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168596 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7168596 : Nat := 118140960795 + 7168596 * 2 ^ 59
def prefixEnd_7168596 : Nat := 4983230072969 + 3 ^ 40 * 7168596 * 2
def baseEnd_7168596 : Nat := 3680935365898140068882233

theorem tailTrace_7168596 : CollatzResearch.WordTrace tailWord_7168596 prefixEnd_7168596 3680935365898140068882233 := by
  unfold tailWord_7168596
  simp only [CollatzResearch.WordTrace]
  refine ⟨130730087968704232785254821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174306783958272310380339761 130730087968704232785254821)
  ·
    refine ⟨24511891494132043647235279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130730087968704232785254821 24511891494132043647235279)
    ·
      refine ⟨36767837241198065470852919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24511891494132043647235279 36767837241198065470852919)
      ·
        refine ⟨55151755861797098206279379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36767837241198065470852919 55151755861797098206279379)
        ·
          refine ⟨82727633792695647309419069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55151755861797098206279379 82727633792695647309419069)
          ·
            refine ⟨31022862672260867741032151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82727633792695647309419069 31022862672260867741032151)
            ·
              refine ⟨46534294008391301611548227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31022862672260867741032151 46534294008391301611548227)
              ·
                refine ⟨69801441012586952417322341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46534294008391301611548227 69801441012586952417322341)
                ·
                  refine ⟨13087770189860053578247939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69801441012586952417322341 13087770189860053578247939)
                  ·
                    refine ⟨19631655284790080367371909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13087770189860053578247939 19631655284790080367371909)
                    ·
                      refine ⟨3680935365898140068882233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19631655284790080367371909 3680935365898140068882233)
                      ·
                        rfl

theorem cell23_7168596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7168596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168596 prefixEnd_7168596 := by exact prefixLift 7168596
  have htrace : WordTrace (prefixWord ++ tailWord_7168596) baseStart_7168596 baseEnd_7168596 := by
    simpa [prefixWord, tailWord_7168596, baseEnd_7168596] using wordTrace_append hprefix tailTrace_7168596
  have hstable : (prefixWord ++ tailWord_7168596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168596).length < 2 ^ (prefixWord ++ tailWord_7168596).sum := by decide
  have hdescent : baseEnd_7168596 < baseStart_7168596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168630 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7168630 : Nat := 118140960795 + 7168630 * 2 ^ 59
def prefixEnd_7168630 : Nat := 4983230072969 + 3 ^ 40 * 7168630 * 2
def baseEnd_7168630 : Nat := 3680952824240392935857077

theorem tailTrace_7168630 : CollatzResearch.WordTrace tailWord_7168630 prefixEnd_7168630 3680952824240392935857077 := by
  unfold tailWord_7168630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16341338501205330586077959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174307610679523526251498229 16341338501205330586077959)
  ·
    refine ⟨24512007751807995879116939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16341338501205330586077959 24512007751807995879116939)
    ·
      refine ⟨36768011627711993818675409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24512007751807995879116939 36768011627711993818675409)
      ·
        refine ⟨27576008720783995364006557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36768011627711993818675409 27576008720783995364006557)
        ·
          refine ⟨10341003270293998261502459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27576008720783995364006557 10341003270293998261502459)
          ·
            refine ⟨15511504905440997392253689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341003270293998261502459 15511504905440997392253689)
            ·
              refine ⟨11633628679080748044190267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511504905440997392253689 11633628679080748044190267)
              ·
                refine ⟨17450443018621122066285401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633628679080748044190267 17450443018621122066285401)
                ·
                  refine ⟨13087832263965841549714051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17450443018621122066285401 13087832263965841549714051)
                  ·
                    refine ⟨19631748395948762324571077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13087832263965841549714051 19631748395948762324571077)
                    ·
                      refine ⟨3680952824240392935857077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19631748395948762324571077 3680952824240392935857077)
                      ·
                        rfl

theorem cell23_7168630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7168630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168630 prefixEnd_7168630 := by exact prefixLift 7168630
  have htrace : WordTrace (prefixWord ++ tailWord_7168630) baseStart_7168630 baseEnd_7168630 := by
    simpa [prefixWord, tailWord_7168630, baseEnd_7168630] using wordTrace_append hprefix tailTrace_7168630
  have hstable : (prefixWord ++ tailWord_7168630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168630).length < 2 ^ (prefixWord ++ tailWord_7168630).sum := by decide
  have hdescent : baseEnd_7168630 < baseStart_7168630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168633 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_7168633 : Nat := 118140960795 + 7168633 * 2 ^ 59
def prefixEnd_7168633 : Nat := 4983230072969 + 3 ^ 40 * 7168633 * 2
def baseEnd_7168633 : Nat := 3680954364682356424119563

theorem tailTrace_7168633 : CollatzResearch.WordTrace tailWord_7168633 prefixEnd_7168633 3680954364682356424119563 := by
  unfold tailWord_7168633
  simp only [CollatzResearch.WordTrace]
  refine ⟨261461525438274420889606553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174307683625516280593071035 261461525438274420889606553)
  ·
    refine ⟨196096144078705815667204915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261461525438274420889606553 196096144078705815667204915)
    ·
      refine ⟨294144216118058723500807373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196096144078705815667204915 294144216118058723500807373)
      ·
        refine ⟨110304081044272021312802765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294144216118058723500807373 110304081044272021312802765)
        ·
          refine ⟨41364030391602007992301037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110304081044272021312802765 41364030391602007992301037)
          ·
            refine ⟨15511511396850752997112889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41364030391602007992301037 15511511396850752997112889)
            ·
              refine ⟨11633633547638064747834667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511511396850752997112889 11633633547638064747834667)
              ·
                refine ⟨17450450321457097121752001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633633547638064747834667 17450450321457097121752001)
                ·
                  refine ⟨13087837741092822841314001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17450450321457097121752001 13087837741092822841314001)
                  ·
                    refine ⟨9815878305819617130985501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13087837741092822841314001 9815878305819617130985501)
                    ·
                      refine ⟨3680954364682356424119563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9815878305819617130985501 3680954364682356424119563)
                      ·
                        rfl

theorem cell23_7168633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_7168633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168633 prefixEnd_7168633 := by exact prefixLift 7168633
  have htrace : WordTrace (prefixWord ++ tailWord_7168633) baseStart_7168633 baseEnd_7168633 := by
    simpa [prefixWord, tailWord_7168633, baseEnd_7168633] using wordTrace_append hprefix tailTrace_7168633
  have hstable : (prefixWord ++ tailWord_7168633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168633).length < 2 ^ (prefixWord ++ tailWord_7168633).sum := by decide
  have hdescent : baseEnd_7168633 < baseStart_7168633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7168656 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2]
def baseStart_7168656 : Nat := 118140960795 + 7168656 * 2 ^ 59
def prefixEnd_7168656 : Nat := 4983230072969 + 3 ^ 40 * 7168656 * 2
def baseEnd_7168656 : Nat := 3680966174737409834131957

theorem tailTrace_7168656 : CollatzResearch.WordTrace tailWord_7168656 prefixEnd_7168656 3680966174737409834131957 := by
  unfold tailWord_7168656
  simp only [CollatzResearch.WordTrace]
  refine ⟨130731182158595547908846911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174308242878127397211795881 130731182158595547908846911)
  ·
    refine ⟨196096773237893321863270367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130731182158595547908846911 196096773237893321863270367)
    ·
      refine ⟨294145159856839982794905551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196096773237893321863270367 294145159856839982794905551)
      ·
        refine ⟨441217739785259974192358327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294145159856839982794905551 441217739785259974192358327)
        ·
          refine ⟨661826609677889961288537491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441217739785259974192358327 661826609677889961288537491)
          ·
            refine ⟨992739914516834941932806237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661826609677889961288537491 992739914516834941932806237)
            ·
              refine ⟨372277467943813103224802339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992739914516834941932806237 372277467943813103224802339)
              ·
                refine ⟨558416201915719654837203509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372277467943813103224802339 558416201915719654837203509)
                ·
                  refine ⟨52351518929598717640987829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558416201915719654837203509 52351518929598717640987829)
                  ·
                    refine ⟨4907954899649879778842609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52351518929598717640987829 4907954899649879778842609)
                    ·
                      refine ⟨3680966174737409834131957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4907954899649879778842609 3680966174737409834131957)
                      ·
                        rfl

theorem cell23_7168656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2].length) (baseStart_7168656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7168656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7168656 prefixEnd_7168656 := by exact prefixLift 7168656
  have htrace : WordTrace (prefixWord ++ tailWord_7168656) baseStart_7168656 baseEnd_7168656 := by
    simpa [prefixWord, tailWord_7168656, baseEnd_7168656] using wordTrace_append hprefix tailTrace_7168656
  have hstable : (prefixWord ++ tailWord_7168656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7168656).length < 2 ^ (prefixWord ++ tailWord_7168656).sum := by decide
  have hdescent : baseEnd_7168656 < baseStart_7168656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7168656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
